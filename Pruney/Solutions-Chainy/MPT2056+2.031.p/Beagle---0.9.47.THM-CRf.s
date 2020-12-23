%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:29 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 264 expanded)
%              Number of leaves         :   46 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  166 ( 720 expanded)
%              Number of equality atoms :   40 ( 167 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_107,axiom,(
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

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_54,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_128,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_83,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_87,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_83])).

tff(c_124,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(u1_struct_0(A_56))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_127,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_124])).

tff(c_129,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_127])).

tff(c_130,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_129])).

tff(c_50,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_46,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_401,plain,(
    ! [A_92,B_93,C_94] :
      ( k7_subset_1(A_92,B_93,C_94) = k4_xboole_0(B_93,C_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_404,plain,(
    ! [C_94] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',C_94) = k4_xboole_0('#skF_4',C_94) ),
    inference(resolution,[status(thm)],[c_44,c_401])).

tff(c_585,plain,(
    ! [A_118,B_119] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_118))),B_119,k1_tarski(k1_xboole_0)) = k2_yellow19(A_118,k3_yellow19(A_118,k2_struct_0(A_118),B_119))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_118)))))
      | ~ v13_waybel_0(B_119,k3_yellow_1(k2_struct_0(A_118)))
      | ~ v2_waybel_0(B_119,k3_yellow_1(k2_struct_0(A_118)))
      | v1_xboole_0(B_119)
      | ~ l1_struct_0(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_587,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_585])).

tff(c_590,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_404,c_587])).

tff(c_591,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52,c_590])).

tff(c_42,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_756,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_42])).

tff(c_20,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_142,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k4_xboole_0(B_61,A_60)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_151,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_142])).

tff(c_154,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_151])).

tff(c_181,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_2'(A_67,B_68),B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),k1_tarski(B_21))
      | B_21 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_103,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden(A_50,B_51)
      | ~ r1_xboole_0(k1_tarski(A_50),B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_107,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden(A_20,k1_tarski(B_21))
      | B_21 = A_20 ) ),
    inference(resolution,[status(thm)],[c_28,c_103])).

tff(c_442,plain,(
    ! [A_99,B_100] :
      ( '#skF_2'(A_99,k1_tarski(B_100)) = B_100
      | r1_xboole_0(A_99,k1_tarski(B_100)) ) ),
    inference(resolution,[status(thm)],[c_181,c_107])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_948,plain,(
    ! [A_143,B_144] :
      ( k3_xboole_0(A_143,k1_tarski(B_144)) = k1_xboole_0
      | '#skF_2'(A_143,k1_tarski(B_144)) = B_144 ) ),
    inference(resolution,[status(thm)],[c_442,c_6])).

tff(c_18,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_980,plain,(
    ! [A_143,B_144] :
      ( k4_xboole_0(A_143,k1_tarski(B_144)) = k5_xboole_0(A_143,k1_xboole_0)
      | '#skF_2'(A_143,k1_tarski(B_144)) = B_144 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_18])).

tff(c_1129,plain,(
    ! [A_151,B_152] :
      ( k4_xboole_0(A_151,k1_tarski(B_152)) = A_151
      | '#skF_2'(A_151,k1_tarski(B_152)) = B_152 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_980])).

tff(c_1173,plain,(
    '#skF_2'('#skF_4',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_756])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1196,plain,
    ( r2_hidden(k1_xboole_0,'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_16])).

tff(c_1209,plain,(
    r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1196])).

tff(c_1216,plain,(
    k3_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1209,c_6])).

tff(c_1229,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1216,c_18])).

tff(c_1243,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1229])).

tff(c_1245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_1243])).

tff(c_1247,plain,(
    ~ r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1196])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_534,plain,(
    ! [C_109,B_110,A_111] :
      ( ~ v1_xboole_0(C_109)
      | ~ r2_hidden(C_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_111))))
      | ~ v13_waybel_0(B_110,k3_yellow_1(A_111))
      | ~ v2_waybel_0(B_110,k3_yellow_1(A_111))
      | ~ v1_subset_1(B_110,u1_struct_0(k3_yellow_1(A_111)))
      | v1_xboole_0(B_110)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1309,plain,(
    ! [A_154,B_155,A_156] :
      ( ~ v1_xboole_0('#skF_2'(A_154,B_155))
      | ~ m1_subset_1(A_154,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_156))))
      | ~ v13_waybel_0(A_154,k3_yellow_1(A_156))
      | ~ v2_waybel_0(A_154,k3_yellow_1(A_156))
      | ~ v1_subset_1(A_154,u1_struct_0(k3_yellow_1(A_156)))
      | v1_xboole_0(A_154)
      | v1_xboole_0(A_156)
      | r1_xboole_0(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_16,c_534])).

tff(c_1311,plain,(
    ! [A_156] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_156))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_156))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_156))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_156)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_156)
      | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_1309])).

tff(c_1321,plain,(
    ! [A_156] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_156))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_156))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_156))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_156)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_156)
      | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1311])).

tff(c_1371,plain,(
    ! [A_157] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_157))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_157))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_157))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_157)))
      | v1_xboole_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1247,c_52,c_1321])).

tff(c_1374,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_1371])).

tff(c_1377,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1374])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:56:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.70  
% 3.49/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.70  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.49/1.70  
% 3.49/1.70  %Foreground sorts:
% 3.49/1.70  
% 3.49/1.70  
% 3.49/1.70  %Background operators:
% 3.49/1.70  
% 3.49/1.70  
% 3.49/1.70  %Foreground operators:
% 3.49/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.49/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.70  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.49/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.70  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.49/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.70  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.49/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.49/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.70  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.49/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.49/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.49/1.70  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.49/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.70  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.49/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.49/1.70  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.49/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.49/1.70  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.49/1.70  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.49/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.49/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.70  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.49/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.70  
% 3.49/1.72  tff(f_148, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.49/1.72  tff(f_80, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.49/1.72  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.49/1.72  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.49/1.72  tff(f_107, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.49/1.72  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.49/1.72  tff(f_60, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.49/1.72  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.49/1.72  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.49/1.72  tff(f_72, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.49/1.72  tff(f_67, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.49/1.72  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.49/1.72  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.49/1.72  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.49/1.72  tff(f_128, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.49/1.72  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.72  tff(c_54, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.72  tff(c_83, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.49/1.72  tff(c_87, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_83])).
% 3.49/1.72  tff(c_124, plain, (![A_56]: (~v1_xboole_0(u1_struct_0(A_56)) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.49/1.72  tff(c_127, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_87, c_124])).
% 3.49/1.72  tff(c_129, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_127])).
% 3.49/1.72  tff(c_130, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_129])).
% 3.49/1.72  tff(c_50, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.72  tff(c_48, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.72  tff(c_46, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.72  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.72  tff(c_52, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.72  tff(c_401, plain, (![A_92, B_93, C_94]: (k7_subset_1(A_92, B_93, C_94)=k4_xboole_0(B_93, C_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.49/1.72  tff(c_404, plain, (![C_94]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', C_94)=k4_xboole_0('#skF_4', C_94))), inference(resolution, [status(thm)], [c_44, c_401])).
% 3.49/1.72  tff(c_585, plain, (![A_118, B_119]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_118))), B_119, k1_tarski(k1_xboole_0))=k2_yellow19(A_118, k3_yellow19(A_118, k2_struct_0(A_118), B_119)) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_118))))) | ~v13_waybel_0(B_119, k3_yellow_1(k2_struct_0(A_118))) | ~v2_waybel_0(B_119, k3_yellow_1(k2_struct_0(A_118))) | v1_xboole_0(B_119) | ~l1_struct_0(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.72  tff(c_587, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_585])).
% 3.49/1.72  tff(c_590, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_404, c_587])).
% 3.49/1.72  tff(c_591, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_52, c_590])).
% 3.49/1.72  tff(c_42, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.72  tff(c_756, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_591, c_42])).
% 3.49/1.72  tff(c_20, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.49/1.72  tff(c_22, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.72  tff(c_142, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k4_xboole_0(B_61, A_60))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.49/1.72  tff(c_151, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_142])).
% 3.49/1.72  tff(c_154, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_151])).
% 3.49/1.72  tff(c_181, plain, (![A_67, B_68]: (r2_hidden('#skF_2'(A_67, B_68), B_68) | r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.72  tff(c_28, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), k1_tarski(B_21)) | B_21=A_20)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.49/1.72  tff(c_103, plain, (![A_50, B_51]: (~r2_hidden(A_50, B_51) | ~r1_xboole_0(k1_tarski(A_50), B_51))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.49/1.72  tff(c_107, plain, (![A_20, B_21]: (~r2_hidden(A_20, k1_tarski(B_21)) | B_21=A_20)), inference(resolution, [status(thm)], [c_28, c_103])).
% 3.49/1.72  tff(c_442, plain, (![A_99, B_100]: ('#skF_2'(A_99, k1_tarski(B_100))=B_100 | r1_xboole_0(A_99, k1_tarski(B_100)))), inference(resolution, [status(thm)], [c_181, c_107])).
% 3.49/1.72  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.72  tff(c_948, plain, (![A_143, B_144]: (k3_xboole_0(A_143, k1_tarski(B_144))=k1_xboole_0 | '#skF_2'(A_143, k1_tarski(B_144))=B_144)), inference(resolution, [status(thm)], [c_442, c_6])).
% 3.49/1.72  tff(c_18, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.49/1.72  tff(c_980, plain, (![A_143, B_144]: (k4_xboole_0(A_143, k1_tarski(B_144))=k5_xboole_0(A_143, k1_xboole_0) | '#skF_2'(A_143, k1_tarski(B_144))=B_144)), inference(superposition, [status(thm), theory('equality')], [c_948, c_18])).
% 3.49/1.72  tff(c_1129, plain, (![A_151, B_152]: (k4_xboole_0(A_151, k1_tarski(B_152))=A_151 | '#skF_2'(A_151, k1_tarski(B_152))=B_152)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_980])).
% 3.49/1.72  tff(c_1173, plain, ('#skF_2'('#skF_4', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1129, c_756])).
% 3.49/1.72  tff(c_16, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.72  tff(c_1196, plain, (r2_hidden(k1_xboole_0, '#skF_4') | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1173, c_16])).
% 3.49/1.72  tff(c_1209, plain, (r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1196])).
% 3.49/1.72  tff(c_1216, plain, (k3_xboole_0('#skF_4', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_1209, c_6])).
% 3.49/1.72  tff(c_1229, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1216, c_18])).
% 3.49/1.72  tff(c_1243, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1229])).
% 3.49/1.72  tff(c_1245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_756, c_1243])).
% 3.49/1.72  tff(c_1247, plain, (~r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1196])).
% 3.49/1.72  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.49/1.72  tff(c_534, plain, (![C_109, B_110, A_111]: (~v1_xboole_0(C_109) | ~r2_hidden(C_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_111)))) | ~v13_waybel_0(B_110, k3_yellow_1(A_111)) | ~v2_waybel_0(B_110, k3_yellow_1(A_111)) | ~v1_subset_1(B_110, u1_struct_0(k3_yellow_1(A_111))) | v1_xboole_0(B_110) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.49/1.72  tff(c_1309, plain, (![A_154, B_155, A_156]: (~v1_xboole_0('#skF_2'(A_154, B_155)) | ~m1_subset_1(A_154, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_156)))) | ~v13_waybel_0(A_154, k3_yellow_1(A_156)) | ~v2_waybel_0(A_154, k3_yellow_1(A_156)) | ~v1_subset_1(A_154, u1_struct_0(k3_yellow_1(A_156))) | v1_xboole_0(A_154) | v1_xboole_0(A_156) | r1_xboole_0(A_154, B_155))), inference(resolution, [status(thm)], [c_16, c_534])).
% 3.49/1.72  tff(c_1311, plain, (![A_156]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_156)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_156)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_156)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_156))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_156) | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1173, c_1309])).
% 3.49/1.72  tff(c_1321, plain, (![A_156]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_156)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_156)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_156)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_156))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_156) | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1311])).
% 3.49/1.72  tff(c_1371, plain, (![A_157]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_157)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_157)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_157)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_157))) | v1_xboole_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_1247, c_52, c_1321])).
% 3.49/1.72  tff(c_1374, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_1371])).
% 3.49/1.72  tff(c_1377, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1374])).
% 3.49/1.72  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_1377])).
% 3.49/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.72  
% 3.49/1.72  Inference rules
% 3.49/1.72  ----------------------
% 3.49/1.72  #Ref     : 0
% 3.49/1.72  #Sup     : 309
% 3.49/1.72  #Fact    : 0
% 3.49/1.72  #Define  : 0
% 3.49/1.72  #Split   : 2
% 3.49/1.72  #Chain   : 0
% 3.49/1.72  #Close   : 0
% 3.49/1.72  
% 3.49/1.72  Ordering : KBO
% 3.49/1.72  
% 3.49/1.72  Simplification rules
% 3.49/1.72  ----------------------
% 3.49/1.72  #Subsume      : 49
% 3.49/1.72  #Demod        : 67
% 3.49/1.72  #Tautology    : 155
% 3.49/1.72  #SimpNegUnit  : 14
% 3.49/1.72  #BackRed      : 1
% 3.49/1.72  
% 3.49/1.72  #Partial instantiations: 0
% 3.49/1.72  #Strategies tried      : 1
% 3.49/1.72  
% 3.49/1.72  Timing (in seconds)
% 3.49/1.72  ----------------------
% 3.49/1.72  Preprocessing        : 0.38
% 3.49/1.72  Parsing              : 0.21
% 3.49/1.72  CNF conversion       : 0.03
% 3.49/1.72  Main loop            : 0.43
% 3.49/1.72  Inferencing          : 0.17
% 3.49/1.72  Reduction            : 0.13
% 3.49/1.72  Demodulation         : 0.08
% 3.49/1.72  BG Simplification    : 0.03
% 3.49/1.72  Subsumption          : 0.08
% 3.49/1.72  Abstraction          : 0.02
% 3.49/1.72  MUC search           : 0.00
% 3.49/1.72  Cooper               : 0.00
% 3.49/1.72  Total                : 0.84
% 3.49/1.72  Index Insertion      : 0.00
% 3.49/1.72  Index Deletion       : 0.00
% 3.49/1.72  Index Matching       : 0.00
% 3.49/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
