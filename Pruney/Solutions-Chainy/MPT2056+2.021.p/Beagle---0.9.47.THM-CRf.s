%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:28 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 151 expanded)
%              Number of leaves         :   48 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  162 ( 340 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_151,negated_conjecture,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_110,axiom,(
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

tff(f_131,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_58,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_54,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_52,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_50,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,k3_xboole_0(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_204,plain,(
    ! [A_77,B_78] :
      ( ~ r1_xboole_0(A_77,B_78)
      | v1_xboole_0(k3_xboole_0(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_136,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_102,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(A_56,B_57)
      | ~ r1_xboole_0(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_111,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_102])).

tff(c_161,plain,(
    ! [B_69] : r1_tarski(k1_xboole_0,B_69) ),
    inference(resolution,[status(thm)],[c_136,c_111])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( B_18 = A_17
      | ~ r1_tarski(B_18,A_17)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_169,plain,(
    ! [B_72] :
      ( k1_xboole_0 = B_72
      | ~ r1_tarski(B_72,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_161,c_20])).

tff(c_182,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_151,c_169])).

tff(c_230,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_xboole_0(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_204,c_182])).

tff(c_274,plain,(
    ! [A_89] : k3_xboole_0(A_89,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_230])).

tff(c_26,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_288,plain,(
    ! [A_89] : k5_xboole_0(A_89,k1_xboole_0) = k4_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_26])).

tff(c_300,plain,(
    ! [A_89] : k5_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_288])).

tff(c_97,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(k1_tarski(A_53),B_54)
      | r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [B_54,A_53] :
      ( r1_xboole_0(B_54,k1_tarski(A_53))
      | r2_hidden(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_97,c_14])).

tff(c_448,plain,(
    ! [B_106,A_107] :
      ( k3_xboole_0(B_106,k1_tarski(A_107)) = k1_xboole_0
      | r2_hidden(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_100,c_230])).

tff(c_477,plain,(
    ! [B_106,A_107] :
      ( k4_xboole_0(B_106,k1_tarski(A_107)) = k5_xboole_0(B_106,k1_xboole_0)
      | r2_hidden(A_107,B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_26])).

tff(c_498,plain,(
    ! [B_106,A_107] :
      ( k4_xboole_0(B_106,k1_tarski(A_107)) = B_106
      | r2_hidden(A_107,B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_477])).

tff(c_444,plain,(
    ! [A_103,B_104,C_105] :
      ( k7_subset_1(A_103,B_104,C_105) = k4_xboole_0(B_104,C_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_447,plain,(
    ! [C_105] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_105) = k4_xboole_0('#skF_5',C_105) ),
    inference(resolution,[status(thm)],[c_48,c_444])).

tff(c_700,plain,(
    ! [A_129,B_130] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_129))),B_130,k1_tarski(k1_xboole_0)) = k2_yellow19(A_129,k3_yellow19(A_129,k2_struct_0(A_129),B_130))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_129)))))
      | ~ v13_waybel_0(B_130,k3_yellow_1(k2_struct_0(A_129)))
      | ~ v2_waybel_0(B_130,k3_yellow_1(k2_struct_0(A_129)))
      | v1_xboole_0(B_130)
      | ~ l1_struct_0(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_702,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_700])).

tff(c_705,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_447,c_702])).

tff(c_706,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_705])).

tff(c_46,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_770,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_46])).

tff(c_778,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_770])).

tff(c_44,plain,(
    ! [C_41,B_39,A_35] :
      ( ~ v1_xboole_0(C_41)
      | ~ r2_hidden(C_41,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v2_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v1_subset_1(B_39,u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0(B_39)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_805,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_778,c_44])).

tff(c_813,plain,(
    ! [A_35] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_805])).

tff(c_848,plain,(
    ! [A_143] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_143))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_143))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_143))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_143)))
      | v1_xboole_0(A_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_813])).

tff(c_851,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_848])).

tff(c_854,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_851])).

tff(c_38,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k2_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_864,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_854,c_38])).

tff(c_870,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_864])).

tff(c_872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.51  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.25/1.51  
% 3.25/1.51  %Foreground sorts:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Background operators:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Foreground operators:
% 3.25/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.51  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.25/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.25/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.51  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.25/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.25/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.51  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.25/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.25/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.51  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.25/1.51  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.25/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.25/1.51  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.25/1.51  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.25/1.51  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.25/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.25/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.25/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.51  
% 3.25/1.53  tff(f_151, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.25/1.53  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.25/1.53  tff(f_67, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.25/1.53  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.25/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.25/1.53  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.25/1.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.25/1.53  tff(f_74, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.25/1.53  tff(f_63, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.25/1.53  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.25/1.53  tff(f_79, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.25/1.53  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.25/1.53  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.25/1.53  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.25/1.53  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.25/1.53  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.25/1.53  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.25/1.53  tff(c_58, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.25/1.53  tff(c_54, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.25/1.53  tff(c_52, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.25/1.53  tff(c_50, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.25/1.53  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.25/1.53  tff(c_56, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.25/1.53  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.53  tff(c_28, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.25/1.53  tff(c_30, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.25/1.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.53  tff(c_187, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, k3_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.53  tff(c_204, plain, (![A_77, B_78]: (~r1_xboole_0(A_77, B_78) | v1_xboole_0(k3_xboole_0(A_77, B_78)))), inference(resolution, [status(thm)], [c_4, c_187])).
% 3.25/1.53  tff(c_136, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.25/1.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.53  tff(c_151, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_136, c_2])).
% 3.25/1.53  tff(c_102, plain, (![A_56, B_57]: (~r2_hidden(A_56, B_57) | ~r1_xboole_0(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.25/1.53  tff(c_111, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_102])).
% 3.25/1.53  tff(c_161, plain, (![B_69]: (r1_tarski(k1_xboole_0, B_69))), inference(resolution, [status(thm)], [c_136, c_111])).
% 3.25/1.53  tff(c_20, plain, (![B_18, A_17]: (B_18=A_17 | ~r1_tarski(B_18, A_17) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.25/1.53  tff(c_169, plain, (![B_72]: (k1_xboole_0=B_72 | ~r1_tarski(B_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_161, c_20])).
% 3.25/1.53  tff(c_182, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_151, c_169])).
% 3.25/1.53  tff(c_230, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_xboole_0(A_83, B_84))), inference(resolution, [status(thm)], [c_204, c_182])).
% 3.25/1.53  tff(c_274, plain, (![A_89]: (k3_xboole_0(A_89, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_230])).
% 3.25/1.53  tff(c_26, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.25/1.53  tff(c_288, plain, (![A_89]: (k5_xboole_0(A_89, k1_xboole_0)=k4_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_274, c_26])).
% 3.25/1.53  tff(c_300, plain, (![A_89]: (k5_xboole_0(A_89, k1_xboole_0)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_288])).
% 3.25/1.53  tff(c_97, plain, (![A_53, B_54]: (r1_xboole_0(k1_tarski(A_53), B_54) | r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.25/1.53  tff(c_14, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_100, plain, (![B_54, A_53]: (r1_xboole_0(B_54, k1_tarski(A_53)) | r2_hidden(A_53, B_54))), inference(resolution, [status(thm)], [c_97, c_14])).
% 3.25/1.53  tff(c_448, plain, (![B_106, A_107]: (k3_xboole_0(B_106, k1_tarski(A_107))=k1_xboole_0 | r2_hidden(A_107, B_106))), inference(resolution, [status(thm)], [c_100, c_230])).
% 3.25/1.53  tff(c_477, plain, (![B_106, A_107]: (k4_xboole_0(B_106, k1_tarski(A_107))=k5_xboole_0(B_106, k1_xboole_0) | r2_hidden(A_107, B_106))), inference(superposition, [status(thm), theory('equality')], [c_448, c_26])).
% 3.25/1.53  tff(c_498, plain, (![B_106, A_107]: (k4_xboole_0(B_106, k1_tarski(A_107))=B_106 | r2_hidden(A_107, B_106))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_477])).
% 3.25/1.53  tff(c_444, plain, (![A_103, B_104, C_105]: (k7_subset_1(A_103, B_104, C_105)=k4_xboole_0(B_104, C_105) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.25/1.53  tff(c_447, plain, (![C_105]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_105)=k4_xboole_0('#skF_5', C_105))), inference(resolution, [status(thm)], [c_48, c_444])).
% 3.25/1.53  tff(c_700, plain, (![A_129, B_130]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_129))), B_130, k1_tarski(k1_xboole_0))=k2_yellow19(A_129, k3_yellow19(A_129, k2_struct_0(A_129), B_130)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_129))))) | ~v13_waybel_0(B_130, k3_yellow_1(k2_struct_0(A_129))) | ~v2_waybel_0(B_130, k3_yellow_1(k2_struct_0(A_129))) | v1_xboole_0(B_130) | ~l1_struct_0(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.25/1.53  tff(c_702, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_700])).
% 3.25/1.53  tff(c_705, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_50, c_447, c_702])).
% 3.25/1.53  tff(c_706, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_705])).
% 3.25/1.53  tff(c_46, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.25/1.53  tff(c_770, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_706, c_46])).
% 3.25/1.53  tff(c_778, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_498, c_770])).
% 3.25/1.53  tff(c_44, plain, (![C_41, B_39, A_35]: (~v1_xboole_0(C_41) | ~r2_hidden(C_41, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0(B_39, k3_yellow_1(A_35)) | ~v2_waybel_0(B_39, k3_yellow_1(A_35)) | ~v1_subset_1(B_39, u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0(B_39) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.25/1.53  tff(c_805, plain, (![A_35]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_778, c_44])).
% 3.25/1.53  tff(c_813, plain, (![A_35]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_805])).
% 3.25/1.53  tff(c_848, plain, (![A_143]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_143)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_143)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_143)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_143))) | v1_xboole_0(A_143))), inference(negUnitSimplification, [status(thm)], [c_56, c_813])).
% 3.25/1.53  tff(c_851, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_848])).
% 3.25/1.53  tff(c_854, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_851])).
% 3.25/1.53  tff(c_38, plain, (![A_30]: (~v1_xboole_0(k2_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.25/1.53  tff(c_864, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_854, c_38])).
% 3.25/1.53  tff(c_870, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_864])).
% 3.25/1.53  tff(c_872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_870])).
% 3.25/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.53  
% 3.25/1.53  Inference rules
% 3.25/1.53  ----------------------
% 3.25/1.53  #Ref     : 0
% 3.25/1.53  #Sup     : 178
% 3.25/1.53  #Fact    : 0
% 3.25/1.53  #Define  : 0
% 3.25/1.53  #Split   : 0
% 3.25/1.53  #Chain   : 0
% 3.25/1.53  #Close   : 0
% 3.25/1.53  
% 3.25/1.53  Ordering : KBO
% 3.25/1.53  
% 3.25/1.53  Simplification rules
% 3.25/1.53  ----------------------
% 3.25/1.53  #Subsume      : 30
% 3.25/1.53  #Demod        : 51
% 3.25/1.53  #Tautology    : 79
% 3.25/1.53  #SimpNegUnit  : 15
% 3.25/1.53  #BackRed      : 1
% 3.25/1.53  
% 3.25/1.53  #Partial instantiations: 0
% 3.25/1.53  #Strategies tried      : 1
% 3.25/1.53  
% 3.25/1.53  Timing (in seconds)
% 3.25/1.53  ----------------------
% 3.25/1.53  Preprocessing        : 0.36
% 3.25/1.53  Parsing              : 0.19
% 3.25/1.53  CNF conversion       : 0.02
% 3.25/1.53  Main loop            : 0.39
% 3.25/1.53  Inferencing          : 0.15
% 3.25/1.53  Reduction            : 0.12
% 3.25/1.53  Demodulation         : 0.08
% 3.25/1.53  BG Simplification    : 0.02
% 3.40/1.53  Subsumption          : 0.07
% 3.40/1.53  Abstraction          : 0.02
% 3.40/1.53  MUC search           : 0.00
% 3.40/1.53  Cooper               : 0.00
% 3.40/1.53  Total                : 0.79
% 3.40/1.53  Index Insertion      : 0.00
% 3.40/1.53  Index Deletion       : 0.00
% 3.40/1.53  Index Matching       : 0.00
% 3.40/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
