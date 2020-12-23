%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:23 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 114 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 184 expanded)
%              Number of equality atoms :   53 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_94,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_87,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k10_relat_1(B_37,A_38),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_90,plain,(
    ! [A_38] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_38),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_87])).

tff(c_91,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_46,plain,(
    ! [A_19] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_146,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_3'(A_64,B_65),B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4880,plain,(
    ! [A_1481,A_1482] :
      ( '#skF_3'(A_1481,k1_tarski(A_1482)) = A_1482
      | k1_tarski(A_1482) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(A_1482),k1_zfmisc_1(A_1481)) ) ),
    inference(resolution,[status(thm)],[c_146,c_12])).

tff(c_5006,plain,(
    ! [A_19] :
      ( '#skF_3'(k1_zfmisc_1(A_19),k1_tarski(k1_xboole_0)) = k1_xboole_0
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_4880])).

tff(c_6489,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5006])).

tff(c_8,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [A_54,C_55,B_56] :
      ( k1_tarski(A_54) = C_55
      | k1_xboole_0 = C_55
      | k2_xboole_0(B_56,C_55) != k1_tarski(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_134,plain,(
    ! [A_3,B_4,A_54] :
      ( k3_xboole_0(A_3,B_4) = k1_tarski(A_54)
      | k3_xboole_0(A_3,B_4) = k1_xboole_0
      | k1_tarski(A_54) != A_3 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_131])).

tff(c_162,plain,(
    ! [A_54,B_4] :
      ( k3_xboole_0(k1_tarski(A_54),B_4) = k1_tarski(A_54)
      | k3_xboole_0(k1_tarski(A_54),B_4) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_134])).

tff(c_216,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(k1_tarski(A_81),B_82) = k1_xboole_0
      | k1_tarski(A_81) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_162])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | k3_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) != k1_tarski(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_230,plain,(
    ! [B_12,A_81] :
      ( B_12 = A_81
      | k1_tarski(A_81) != k1_xboole_0
      | k1_tarski(A_81) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_24])).

tff(c_6572,plain,(
    ! [B_12] :
      ( k1_xboole_0 = B_12
      | k1_tarski(k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6489,c_230])).

tff(c_6744,plain,(
    ! [B_1810] : k1_xboole_0 = B_1810 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6489,c_6572])).

tff(c_50,plain,(
    ! [A_23,B_24,C_25,D_26] : v1_relat_1(k2_tarski(k4_tarski(A_23,B_24),k4_tarski(C_25,D_26))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6818,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6744,c_50])).

tff(c_6878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_6818])).

tff(c_6880,plain,(
    k1_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5006])).

tff(c_6891,plain,(
    ! [A_2451] : '#skF_3'(k1_zfmisc_1(A_2451),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5006])).

tff(c_44,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1('#skF_3'(A_16,B_17),A_16)
      | k1_xboole_0 = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6899,plain,(
    ! [A_2451] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2451))
      | k1_tarski(k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_2451))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6891,c_44])).

tff(c_7262,plain,(
    ! [A_2451] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2451))
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6899])).

tff(c_7296,plain,(
    ! [A_2492] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2492)) ),
    inference(negUnitSimplification,[status(thm)],[c_6880,c_7262])).

tff(c_48,plain,(
    ! [B_22,A_20] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7299,plain,(
    ! [A_2492] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_2492) ) ),
    inference(resolution,[status(thm)],[c_7296,c_48])).

tff(c_7452,plain,(
    ! [A_2492] : ~ v1_relat_1(A_2492) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_7299])).

tff(c_7470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7452,c_50])).

tff(c_7471,plain,(
    ! [A_38] : r1_tarski(k10_relat_1(k1_xboole_0,A_38),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_7474,plain,(
    ! [B_2534,A_2535] :
      ( B_2534 = A_2535
      | ~ r1_tarski(B_2534,A_2535)
      | ~ r1_tarski(A_2535,B_2534) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7476,plain,(
    ! [A_38] :
      ( k10_relat_1(k1_xboole_0,A_38) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,A_38)) ) ),
    inference(resolution,[status(thm)],[c_7471,c_7474])).

tff(c_7485,plain,(
    ! [A_38] : k10_relat_1(k1_xboole_0,A_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7476])).

tff(c_58,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7485,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:44:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.88  
% 4.66/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.88  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.66/1.88  
% 4.66/1.88  %Foreground sorts:
% 4.66/1.88  
% 4.66/1.88  
% 4.66/1.88  %Background operators:
% 4.66/1.88  
% 4.66/1.88  
% 4.66/1.88  %Foreground operators:
% 4.66/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.66/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.66/1.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.66/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.66/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.66/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.66/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.66/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.88  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.66/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.66/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.66/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.66/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.66/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.66/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.66/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.66/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.66/1.88  
% 4.66/1.90  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.66/1.90  tff(f_94, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.66/1.90  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 4.66/1.90  tff(f_78, axiom, (![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 4.66/1.90  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.66/1.90  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.66/1.90  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.66/1.90  tff(f_64, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.66/1.90  tff(f_46, axiom, (![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 4.66/1.90  tff(f_87, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 4.66/1.90  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.66/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.66/1.90  tff(f_97, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 4.66/1.90  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/1.90  tff(c_56, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.66/1.90  tff(c_87, plain, (![B_37, A_38]: (r1_tarski(k10_relat_1(B_37, A_38), k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.66/1.90  tff(c_90, plain, (![A_38]: (r1_tarski(k10_relat_1(k1_xboole_0, A_38), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_56, c_87])).
% 4.66/1.90  tff(c_91, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_90])).
% 4.66/1.90  tff(c_46, plain, (![A_19]: (m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.66/1.90  tff(c_146, plain, (![A_64, B_65]: (r2_hidden('#skF_3'(A_64, B_65), B_65) | k1_xboole_0=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.66/1.90  tff(c_12, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.66/1.90  tff(c_4880, plain, (![A_1481, A_1482]: ('#skF_3'(A_1481, k1_tarski(A_1482))=A_1482 | k1_tarski(A_1482)=k1_xboole_0 | ~m1_subset_1(k1_tarski(A_1482), k1_zfmisc_1(A_1481)))), inference(resolution, [status(thm)], [c_146, c_12])).
% 4.66/1.90  tff(c_5006, plain, (![A_19]: ('#skF_3'(k1_zfmisc_1(A_19), k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_4880])).
% 4.66/1.90  tff(c_6489, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5006])).
% 4.66/1.90  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.66/1.90  tff(c_131, plain, (![A_54, C_55, B_56]: (k1_tarski(A_54)=C_55 | k1_xboole_0=C_55 | k2_xboole_0(B_56, C_55)!=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.66/1.90  tff(c_134, plain, (![A_3, B_4, A_54]: (k3_xboole_0(A_3, B_4)=k1_tarski(A_54) | k3_xboole_0(A_3, B_4)=k1_xboole_0 | k1_tarski(A_54)!=A_3)), inference(superposition, [status(thm), theory('equality')], [c_8, c_131])).
% 4.66/1.90  tff(c_162, plain, (![A_54, B_4]: (k3_xboole_0(k1_tarski(A_54), B_4)=k1_tarski(A_54) | k3_xboole_0(k1_tarski(A_54), B_4)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_134])).
% 4.66/1.90  tff(c_216, plain, (![A_81, B_82]: (k3_xboole_0(k1_tarski(A_81), B_82)=k1_xboole_0 | k1_tarski(A_81)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_162])).
% 4.66/1.90  tff(c_24, plain, (![B_12, A_11]: (B_12=A_11 | k3_xboole_0(k1_tarski(A_11), k1_tarski(B_12))!=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.66/1.90  tff(c_230, plain, (![B_12, A_81]: (B_12=A_81 | k1_tarski(A_81)!=k1_xboole_0 | k1_tarski(A_81)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_24])).
% 4.66/1.90  tff(c_6572, plain, (![B_12]: (k1_xboole_0=B_12 | k1_tarski(k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6489, c_230])).
% 4.66/1.90  tff(c_6744, plain, (![B_1810]: (k1_xboole_0=B_1810)), inference(demodulation, [status(thm), theory('equality')], [c_6489, c_6572])).
% 4.66/1.90  tff(c_50, plain, (![A_23, B_24, C_25, D_26]: (v1_relat_1(k2_tarski(k4_tarski(A_23, B_24), k4_tarski(C_25, D_26))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.66/1.90  tff(c_6818, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6744, c_50])).
% 4.66/1.90  tff(c_6878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_6818])).
% 4.66/1.90  tff(c_6880, plain, (k1_tarski(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_5006])).
% 4.66/1.90  tff(c_6891, plain, (![A_2451]: ('#skF_3'(k1_zfmisc_1(A_2451), k1_tarski(k1_xboole_0))=k1_xboole_0)), inference(splitRight, [status(thm)], [c_5006])).
% 4.66/1.90  tff(c_44, plain, (![A_16, B_17]: (m1_subset_1('#skF_3'(A_16, B_17), A_16) | k1_xboole_0=B_17 | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.66/1.90  tff(c_6899, plain, (![A_2451]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2451)) | k1_tarski(k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_2451))))), inference(superposition, [status(thm), theory('equality')], [c_6891, c_44])).
% 4.66/1.90  tff(c_7262, plain, (![A_2451]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2451)) | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6899])).
% 4.66/1.90  tff(c_7296, plain, (![A_2492]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2492)))), inference(negUnitSimplification, [status(thm)], [c_6880, c_7262])).
% 4.66/1.90  tff(c_48, plain, (![B_22, A_20]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.66/1.90  tff(c_7299, plain, (![A_2492]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_2492))), inference(resolution, [status(thm)], [c_7296, c_48])).
% 4.66/1.90  tff(c_7452, plain, (![A_2492]: (~v1_relat_1(A_2492))), inference(negUnitSimplification, [status(thm)], [c_91, c_7299])).
% 4.66/1.90  tff(c_7470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7452, c_50])).
% 4.66/1.90  tff(c_7471, plain, (![A_38]: (r1_tarski(k10_relat_1(k1_xboole_0, A_38), k1_xboole_0))), inference(splitRight, [status(thm)], [c_90])).
% 4.66/1.90  tff(c_7474, plain, (![B_2534, A_2535]: (B_2534=A_2535 | ~r1_tarski(B_2534, A_2535) | ~r1_tarski(A_2535, B_2534))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.90  tff(c_7476, plain, (![A_38]: (k10_relat_1(k1_xboole_0, A_38)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k10_relat_1(k1_xboole_0, A_38)))), inference(resolution, [status(thm)], [c_7471, c_7474])).
% 4.66/1.90  tff(c_7485, plain, (![A_38]: (k10_relat_1(k1_xboole_0, A_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_7476])).
% 4.66/1.90  tff(c_58, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.66/1.90  tff(c_7496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7485, c_58])).
% 4.66/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.90  
% 4.66/1.90  Inference rules
% 4.66/1.90  ----------------------
% 4.66/1.90  #Ref     : 1
% 4.66/1.90  #Sup     : 1187
% 4.66/1.90  #Fact    : 2
% 4.66/1.90  #Define  : 0
% 4.66/1.90  #Split   : 4
% 4.66/1.90  #Chain   : 0
% 4.66/1.90  #Close   : 0
% 4.66/1.90  
% 4.66/1.90  Ordering : KBO
% 4.66/1.90  
% 4.66/1.90  Simplification rules
% 4.66/1.90  ----------------------
% 4.66/1.90  #Subsume      : 325
% 4.66/1.90  #Demod        : 280
% 4.66/1.90  #Tautology    : 160
% 4.66/1.90  #SimpNegUnit  : 9
% 4.66/1.90  #BackRed      : 5
% 4.66/1.90  
% 4.66/1.90  #Partial instantiations: 1316
% 4.66/1.90  #Strategies tried      : 1
% 4.66/1.90  
% 4.66/1.90  Timing (in seconds)
% 4.66/1.90  ----------------------
% 4.66/1.90  Preprocessing        : 0.30
% 4.66/1.90  Parsing              : 0.17
% 4.66/1.90  CNF conversion       : 0.02
% 4.66/1.90  Main loop            : 0.83
% 4.66/1.90  Inferencing          : 0.31
% 4.66/1.90  Reduction            : 0.23
% 5.03/1.90  Demodulation         : 0.17
% 5.03/1.90  BG Simplification    : 0.05
% 5.03/1.90  Subsumption          : 0.19
% 5.03/1.90  Abstraction          : 0.06
% 5.03/1.90  MUC search           : 0.00
% 5.03/1.90  Cooper               : 0.00
% 5.03/1.90  Total                : 1.16
% 5.03/1.90  Index Insertion      : 0.00
% 5.03/1.90  Index Deletion       : 0.00
% 5.03/1.90  Index Matching       : 0.00
% 5.03/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
