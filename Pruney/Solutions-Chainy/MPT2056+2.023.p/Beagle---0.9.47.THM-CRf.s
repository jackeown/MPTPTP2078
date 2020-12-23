%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:28 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 301 expanded)
%              Number of leaves         :   44 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          :  203 ( 912 expanded)
%              Number of equality atoms :   30 ( 153 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_68,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_66,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_62,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_60,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_58,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_128,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_128])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k4_xboole_0(A_20,B_21) != A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_422,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,B_97)
      | ~ r2_hidden(C_98,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_796,plain,(
    ! [C_144,B_145,A_146] :
      ( ~ r2_hidden(C_144,B_145)
      | ~ r2_hidden(C_144,A_146)
      | k4_xboole_0(A_146,B_145) != A_146 ) ),
    inference(resolution,[status(thm)],[c_34,c_422])).

tff(c_961,plain,(
    ! [A_152,A_153] :
      ( ~ r2_hidden('#skF_1'(A_152),A_153)
      | k4_xboole_0(A_153,A_152) != A_153
      | v1_xboole_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_4,c_796])).

tff(c_977,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_961])).

tff(c_1039,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_977])).

tff(c_548,plain,(
    ! [A_113,B_114,C_115] :
      ( k7_subset_1(A_113,B_114,C_115) = k4_xboole_0(B_114,C_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_551,plain,(
    ! [C_115] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',C_115) = k4_xboole_0('#skF_4',C_115) ),
    inference(resolution,[status(thm)],[c_56,c_548])).

tff(c_776,plain,(
    ! [A_139,B_140] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_139))),B_140,k1_tarski(k1_xboole_0)) = k2_yellow19(A_139,k3_yellow19(A_139,k2_struct_0(A_139),B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_139)))))
      | ~ v13_waybel_0(B_140,k3_yellow_1(k2_struct_0(A_139)))
      | ~ v2_waybel_0(B_140,k3_yellow_1(k2_struct_0(A_139)))
      | v1_xboole_0(B_140)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_778,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_776])).

tff(c_781,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_58,c_551,c_778])).

tff(c_782,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_781])).

tff(c_54,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_873,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_54])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_99,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(A_56,B_57)
      | ~ r1_xboole_0(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_99])).

tff(c_451,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden(A_103,k4_xboole_0(B_104,k1_tarski(C_105)))
      | C_105 = A_103
      | ~ r2_hidden(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_471,plain,(
    ! [A_103,C_105] :
      ( r2_hidden(A_103,k1_xboole_0)
      | C_105 = A_103
      | ~ r2_hidden(A_103,k1_tarski(C_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_451])).

tff(c_479,plain,(
    ! [C_106,A_107] :
      ( C_106 = A_107
      | ~ r2_hidden(A_107,k1_tarski(C_106)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_471])).

tff(c_582,plain,(
    ! [A_120,C_121] :
      ( '#skF_2'(A_120,k1_tarski(C_121)) = C_121
      | r1_xboole_0(A_120,k1_tarski(C_121)) ) ),
    inference(resolution,[status(thm)],[c_10,c_479])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3445,plain,(
    ! [A_281,C_282] :
      ( k4_xboole_0(A_281,k1_tarski(C_282)) = A_281
      | '#skF_2'(A_281,k1_tarski(C_282)) = C_282 ) ),
    inference(resolution,[status(thm)],[c_582,c_32])).

tff(c_3595,plain,(
    '#skF_2'('#skF_4',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3445,c_873])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_708,plain,(
    ! [C_130,B_131,A_132] :
      ( ~ v1_xboole_0(C_130)
      | ~ r2_hidden(C_130,B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132))))
      | ~ v13_waybel_0(B_131,k3_yellow_1(A_132))
      | ~ v2_waybel_0(B_131,k3_yellow_1(A_132))
      | ~ v1_subset_1(B_131,u1_struct_0(k3_yellow_1(A_132)))
      | v1_xboole_0(B_131)
      | v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_719,plain,(
    ! [A_5,B_6,A_132] :
      ( ~ v1_xboole_0('#skF_2'(A_5,B_6))
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132))))
      | ~ v13_waybel_0(A_5,k3_yellow_1(A_132))
      | ~ v2_waybel_0(A_5,k3_yellow_1(A_132))
      | ~ v1_subset_1(A_5,u1_struct_0(k3_yellow_1(A_132)))
      | v1_xboole_0(A_5)
      | v1_xboole_0(A_132)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_708])).

tff(c_3609,plain,(
    ! [A_132] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_132))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_132))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_132)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_132)
      | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3595,c_719])).

tff(c_3625,plain,(
    ! [A_132] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_132))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_132))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_132)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_132)
      | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_3609])).

tff(c_3626,plain,(
    ! [A_132] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_132))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_132))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_132)))
      | v1_xboole_0(A_132)
      | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3625])).

tff(c_3723,plain,(
    r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_3626])).

tff(c_3728,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3723,c_32])).

tff(c_3733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_3728])).

tff(c_3735,plain,(
    ~ r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3626])).

tff(c_3618,plain,
    ( r2_hidden(k1_xboole_0,'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3595,c_12])).

tff(c_3776,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3735,c_3618])).

tff(c_52,plain,(
    ! [C_41,B_39,A_35] :
      ( ~ v1_xboole_0(C_41)
      | ~ r2_hidden(C_41,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v2_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v1_subset_1(B_39,u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0(B_39)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3787,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_3776,c_52])).

tff(c_3799,plain,(
    ! [A_35] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_3787])).

tff(c_3917,plain,(
    ! [A_298] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_298))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_298))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_298))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_298)))
      | v1_xboole_0(A_298) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3799])).

tff(c_3920,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_3917])).

tff(c_3923,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_3920])).

tff(c_46,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k2_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3930,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3923,c_46])).

tff(c_3935,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3930])).

tff(c_3937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3935])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:07:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.86  
% 4.77/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.86  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.77/1.86  
% 4.77/1.86  %Foreground sorts:
% 4.77/1.86  
% 4.77/1.86  
% 4.77/1.86  %Background operators:
% 4.77/1.86  
% 4.77/1.86  
% 4.77/1.86  %Foreground operators:
% 4.77/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.77/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.86  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.77/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.86  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.77/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.77/1.86  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.77/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.77/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.77/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.86  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.77/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.77/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.77/1.86  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.77/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.86  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.77/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.77/1.86  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.77/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.77/1.86  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.77/1.86  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.77/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.77/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.77/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.77/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.77/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.86  
% 4.77/1.88  tff(f_156, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 4.77/1.88  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.77/1.88  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.77/1.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.77/1.88  tff(f_72, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.77/1.88  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.77/1.88  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.77/1.88  tff(f_115, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 4.77/1.88  tff(f_68, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.77/1.88  tff(f_77, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 4.77/1.88  tff(f_84, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.77/1.88  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 4.77/1.88  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 4.77/1.88  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.77/1.88  tff(c_66, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.77/1.88  tff(c_62, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.77/1.88  tff(c_60, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.77/1.88  tff(c_58, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.77/1.88  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.77/1.88  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.77/1.88  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.77/1.88  tff(c_128, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.77/1.88  tff(c_136, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_128])).
% 4.77/1.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.88  tff(c_34, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k4_xboole_0(A_20, B_21)!=A_20)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.77/1.88  tff(c_422, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, B_97) | ~r2_hidden(C_98, A_96))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/1.88  tff(c_796, plain, (![C_144, B_145, A_146]: (~r2_hidden(C_144, B_145) | ~r2_hidden(C_144, A_146) | k4_xboole_0(A_146, B_145)!=A_146)), inference(resolution, [status(thm)], [c_34, c_422])).
% 4.77/1.88  tff(c_961, plain, (![A_152, A_153]: (~r2_hidden('#skF_1'(A_152), A_153) | k4_xboole_0(A_153, A_152)!=A_153 | v1_xboole_0(A_152))), inference(resolution, [status(thm)], [c_4, c_796])).
% 4.77/1.88  tff(c_977, plain, (![A_1]: (k4_xboole_0(A_1, A_1)!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_961])).
% 4.77/1.88  tff(c_1039, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_977])).
% 4.77/1.88  tff(c_548, plain, (![A_113, B_114, C_115]: (k7_subset_1(A_113, B_114, C_115)=k4_xboole_0(B_114, C_115) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.77/1.88  tff(c_551, plain, (![C_115]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', C_115)=k4_xboole_0('#skF_4', C_115))), inference(resolution, [status(thm)], [c_56, c_548])).
% 4.77/1.88  tff(c_776, plain, (![A_139, B_140]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_139))), B_140, k1_tarski(k1_xboole_0))=k2_yellow19(A_139, k3_yellow19(A_139, k2_struct_0(A_139), B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_139))))) | ~v13_waybel_0(B_140, k3_yellow_1(k2_struct_0(A_139))) | ~v2_waybel_0(B_140, k3_yellow_1(k2_struct_0(A_139))) | v1_xboole_0(B_140) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.77/1.88  tff(c_778, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_776])).
% 4.77/1.88  tff(c_781, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_58, c_551, c_778])).
% 4.77/1.88  tff(c_782, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_781])).
% 4.77/1.88  tff(c_54, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.77/1.88  tff(c_873, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_782, c_54])).
% 4.77/1.88  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/1.88  tff(c_30, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.77/1.88  tff(c_99, plain, (![A_56, B_57]: (~r2_hidden(A_56, B_57) | ~r1_xboole_0(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.77/1.88  tff(c_109, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_99])).
% 4.77/1.88  tff(c_451, plain, (![A_103, B_104, C_105]: (r2_hidden(A_103, k4_xboole_0(B_104, k1_tarski(C_105))) | C_105=A_103 | ~r2_hidden(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.77/1.88  tff(c_471, plain, (![A_103, C_105]: (r2_hidden(A_103, k1_xboole_0) | C_105=A_103 | ~r2_hidden(A_103, k1_tarski(C_105)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_451])).
% 4.77/1.88  tff(c_479, plain, (![C_106, A_107]: (C_106=A_107 | ~r2_hidden(A_107, k1_tarski(C_106)))), inference(negUnitSimplification, [status(thm)], [c_109, c_471])).
% 4.77/1.88  tff(c_582, plain, (![A_120, C_121]: ('#skF_2'(A_120, k1_tarski(C_121))=C_121 | r1_xboole_0(A_120, k1_tarski(C_121)))), inference(resolution, [status(thm)], [c_10, c_479])).
% 4.77/1.88  tff(c_32, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.77/1.88  tff(c_3445, plain, (![A_281, C_282]: (k4_xboole_0(A_281, k1_tarski(C_282))=A_281 | '#skF_2'(A_281, k1_tarski(C_282))=C_282)), inference(resolution, [status(thm)], [c_582, c_32])).
% 4.77/1.88  tff(c_3595, plain, ('#skF_2'('#skF_4', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3445, c_873])).
% 4.77/1.88  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/1.88  tff(c_708, plain, (![C_130, B_131, A_132]: (~v1_xboole_0(C_130) | ~r2_hidden(C_130, B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132)))) | ~v13_waybel_0(B_131, k3_yellow_1(A_132)) | ~v2_waybel_0(B_131, k3_yellow_1(A_132)) | ~v1_subset_1(B_131, u1_struct_0(k3_yellow_1(A_132))) | v1_xboole_0(B_131) | v1_xboole_0(A_132))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.77/1.88  tff(c_719, plain, (![A_5, B_6, A_132]: (~v1_xboole_0('#skF_2'(A_5, B_6)) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132)))) | ~v13_waybel_0(A_5, k3_yellow_1(A_132)) | ~v2_waybel_0(A_5, k3_yellow_1(A_132)) | ~v1_subset_1(A_5, u1_struct_0(k3_yellow_1(A_132))) | v1_xboole_0(A_5) | v1_xboole_0(A_132) | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_708])).
% 4.77/1.88  tff(c_3609, plain, (![A_132]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_132)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_132)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_132))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_132) | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_3595, c_719])).
% 4.77/1.88  tff(c_3625, plain, (![A_132]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_132)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_132)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_132))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_132) | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_3609])).
% 4.77/1.88  tff(c_3626, plain, (![A_132]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_132)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_132)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_132))) | v1_xboole_0(A_132) | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_64, c_3625])).
% 4.77/1.88  tff(c_3723, plain, (r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3626])).
% 4.77/1.88  tff(c_3728, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))='#skF_4'), inference(resolution, [status(thm)], [c_3723, c_32])).
% 4.77/1.88  tff(c_3733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_873, c_3728])).
% 4.77/1.88  tff(c_3735, plain, (~r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(splitRight, [status(thm)], [c_3626])).
% 4.77/1.88  tff(c_3618, plain, (r2_hidden(k1_xboole_0, '#skF_4') | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3595, c_12])).
% 4.77/1.88  tff(c_3776, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3735, c_3618])).
% 4.77/1.88  tff(c_52, plain, (![C_41, B_39, A_35]: (~v1_xboole_0(C_41) | ~r2_hidden(C_41, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0(B_39, k3_yellow_1(A_35)) | ~v2_waybel_0(B_39, k3_yellow_1(A_35)) | ~v1_subset_1(B_39, u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0(B_39) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.77/1.88  tff(c_3787, plain, (![A_35]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_3776, c_52])).
% 4.77/1.88  tff(c_3799, plain, (![A_35]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_3787])).
% 4.77/1.88  tff(c_3917, plain, (![A_298]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_298)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_298)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_298)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_298))) | v1_xboole_0(A_298))), inference(negUnitSimplification, [status(thm)], [c_64, c_3799])).
% 4.77/1.88  tff(c_3920, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_3917])).
% 4.77/1.88  tff(c_3923, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_3920])).
% 4.77/1.88  tff(c_46, plain, (![A_30]: (~v1_xboole_0(k2_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.77/1.88  tff(c_3930, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3923, c_46])).
% 4.77/1.88  tff(c_3935, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3930])).
% 4.77/1.88  tff(c_3937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3935])).
% 4.77/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.88  
% 4.77/1.88  Inference rules
% 4.77/1.88  ----------------------
% 4.77/1.88  #Ref     : 1
% 4.77/1.88  #Sup     : 952
% 4.77/1.88  #Fact    : 0
% 4.77/1.88  #Define  : 0
% 4.77/1.88  #Split   : 4
% 4.77/1.88  #Chain   : 0
% 4.77/1.88  #Close   : 0
% 4.77/1.88  
% 4.77/1.88  Ordering : KBO
% 4.77/1.88  
% 4.77/1.88  Simplification rules
% 4.77/1.88  ----------------------
% 4.77/1.88  #Subsume      : 306
% 4.77/1.88  #Demod        : 237
% 4.77/1.88  #Tautology    : 361
% 4.77/1.88  #SimpNegUnit  : 22
% 4.77/1.88  #BackRed      : 2
% 4.77/1.88  
% 4.77/1.88  #Partial instantiations: 0
% 4.77/1.88  #Strategies tried      : 1
% 4.77/1.88  
% 4.77/1.88  Timing (in seconds)
% 4.77/1.88  ----------------------
% 4.77/1.88  Preprocessing        : 0.34
% 4.77/1.88  Parsing              : 0.19
% 4.77/1.88  CNF conversion       : 0.02
% 4.77/1.88  Main loop            : 0.78
% 4.77/1.88  Inferencing          : 0.26
% 4.77/1.88  Reduction            : 0.25
% 4.77/1.89  Demodulation         : 0.17
% 4.77/1.89  BG Simplification    : 0.03
% 4.77/1.89  Subsumption          : 0.17
% 4.77/1.89  Abstraction          : 0.04
% 4.77/1.89  MUC search           : 0.00
% 4.77/1.89  Cooper               : 0.00
% 4.77/1.89  Total                : 1.16
% 4.77/1.89  Index Insertion      : 0.00
% 4.77/1.89  Index Deletion       : 0.00
% 4.77/1.89  Index Matching       : 0.00
% 4.77/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
