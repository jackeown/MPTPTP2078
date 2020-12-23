%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:46 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 269 expanded)
%              Number of leaves         :   41 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 ( 589 expanded)
%              Number of equality atoms :   48 ( 185 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_152,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_165,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_40,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2274,plain,(
    ! [A_259,B_260,C_261,D_262] :
      ( k7_relset_1(A_259,B_260,C_261,D_262) = k9_relat_1(C_261,D_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2288,plain,(
    ! [D_262] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_262) = k9_relat_1('#skF_4',D_262) ),
    inference(resolution,[status(thm)],[c_64,c_2274])).

tff(c_2192,plain,(
    ! [B_248,A_249] :
      ( k1_tarski(k1_funct_1(B_248,A_249)) = k2_relat_1(B_248)
      | k1_tarski(A_249) != k1_relat_1(B_248)
      | ~ v1_funct_1(B_248)
      | ~ v1_relat_1(B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2198,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2192,c_60])).

tff(c_2210,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_68,c_2198])).

tff(c_2310,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2288,c_2210])).

tff(c_2311,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2310])).

tff(c_254,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_269,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_254])).

tff(c_38,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2356,plain,(
    ! [B_270,C_271,A_272] :
      ( k2_tarski(B_270,C_271) = A_272
      | k1_tarski(C_271) = A_272
      | k1_tarski(B_270) = A_272
      | k1_xboole_0 = A_272
      | ~ r1_tarski(A_272,k2_tarski(B_270,C_271)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2369,plain,(
    ! [A_4,A_272] :
      ( k2_tarski(A_4,A_4) = A_272
      | k1_tarski(A_4) = A_272
      | k1_tarski(A_4) = A_272
      | k1_xboole_0 = A_272
      | ~ r1_tarski(A_272,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2356])).

tff(c_3266,plain,(
    ! [A_357,A_358] :
      ( k1_tarski(A_357) = A_358
      | k1_tarski(A_357) = A_358
      | k1_tarski(A_357) = A_358
      | k1_xboole_0 = A_358
      | ~ r1_tarski(A_358,k1_tarski(A_357)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2369])).

tff(c_3287,plain,(
    ! [A_359,B_360] :
      ( k1_tarski(A_359) = k1_relat_1(B_360)
      | k1_relat_1(B_360) = k1_xboole_0
      | ~ v4_relat_1(B_360,k1_tarski(A_359))
      | ~ v1_relat_1(B_360) ) ),
    inference(resolution,[status(thm)],[c_38,c_3266])).

tff(c_3329,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_269,c_3287])).

tff(c_3349,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_3329])).

tff(c_3350,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2311,c_3349])).

tff(c_2150,plain,(
    ! [A_247] :
      ( m1_subset_1(A_247,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_247),k2_relat_1(A_247))))
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2169,plain,(
    ! [A_247] :
      ( r1_tarski(A_247,k2_zfmisc_1(k1_relat_1(A_247),k2_relat_1(A_247)))
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(resolution,[status(thm)],[c_2150,c_32])).

tff(c_3397,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3350,c_2169])).

tff(c_3450,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_68,c_30,c_3397])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_218,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_239,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_218])).

tff(c_3486,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3450,c_239])).

tff(c_3537,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_8])).

tff(c_42,plain,(
    ! [A_21] : k9_relat_1(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3534,plain,(
    ! [A_21] : k9_relat_1('#skF_4',A_21) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_3486,c_42])).

tff(c_2295,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2288,c_60])).

tff(c_3783,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_2295])).

tff(c_3787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3537,c_3783])).

tff(c_3788,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2310])).

tff(c_3903,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_3788])).

tff(c_3907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_3903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.00  
% 5.19/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.00  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.19/2.00  
% 5.19/2.00  %Foreground sorts:
% 5.19/2.00  
% 5.19/2.00  
% 5.19/2.00  %Background operators:
% 5.19/2.00  
% 5.19/2.00  
% 5.19/2.00  %Foreground operators:
% 5.19/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.19/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.19/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.19/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.19/2.00  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.19/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.19/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.19/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.19/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.19/2.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.19/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.19/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.19/2.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.19/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/2.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.19/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.19/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.19/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.19/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/2.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.19/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.19/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/2.00  
% 5.19/2.01  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.19/2.01  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.19/2.01  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.19/2.01  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.19/2.01  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.19/2.01  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.19/2.01  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.19/2.01  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.19/2.01  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.19/2.01  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.19/2.01  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.19/2.01  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.19/2.01  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.19/2.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.19/2.01  tff(f_76, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 5.19/2.01  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.19/2.01  tff(c_152, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.19/2.01  tff(c_165, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_152])).
% 5.19/2.01  tff(c_40, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.19/2.01  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.19/2.01  tff(c_30, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.19/2.01  tff(c_2274, plain, (![A_259, B_260, C_261, D_262]: (k7_relset_1(A_259, B_260, C_261, D_262)=k9_relat_1(C_261, D_262) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.19/2.01  tff(c_2288, plain, (![D_262]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_262)=k9_relat_1('#skF_4', D_262))), inference(resolution, [status(thm)], [c_64, c_2274])).
% 5.19/2.01  tff(c_2192, plain, (![B_248, A_249]: (k1_tarski(k1_funct_1(B_248, A_249))=k2_relat_1(B_248) | k1_tarski(A_249)!=k1_relat_1(B_248) | ~v1_funct_1(B_248) | ~v1_relat_1(B_248))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.19/2.01  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.19/2.01  tff(c_2198, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2192, c_60])).
% 5.19/2.01  tff(c_2210, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_68, c_2198])).
% 5.19/2.01  tff(c_2310, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2288, c_2210])).
% 5.19/2.01  tff(c_2311, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2310])).
% 5.19/2.01  tff(c_254, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.19/2.01  tff(c_269, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_254])).
% 5.19/2.01  tff(c_38, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.19/2.01  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.19/2.01  tff(c_2356, plain, (![B_270, C_271, A_272]: (k2_tarski(B_270, C_271)=A_272 | k1_tarski(C_271)=A_272 | k1_tarski(B_270)=A_272 | k1_xboole_0=A_272 | ~r1_tarski(A_272, k2_tarski(B_270, C_271)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.19/2.01  tff(c_2369, plain, (![A_4, A_272]: (k2_tarski(A_4, A_4)=A_272 | k1_tarski(A_4)=A_272 | k1_tarski(A_4)=A_272 | k1_xboole_0=A_272 | ~r1_tarski(A_272, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2356])).
% 5.19/2.01  tff(c_3266, plain, (![A_357, A_358]: (k1_tarski(A_357)=A_358 | k1_tarski(A_357)=A_358 | k1_tarski(A_357)=A_358 | k1_xboole_0=A_358 | ~r1_tarski(A_358, k1_tarski(A_357)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2369])).
% 5.19/2.01  tff(c_3287, plain, (![A_359, B_360]: (k1_tarski(A_359)=k1_relat_1(B_360) | k1_relat_1(B_360)=k1_xboole_0 | ~v4_relat_1(B_360, k1_tarski(A_359)) | ~v1_relat_1(B_360))), inference(resolution, [status(thm)], [c_38, c_3266])).
% 5.19/2.01  tff(c_3329, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_269, c_3287])).
% 5.19/2.01  tff(c_3349, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_165, c_3329])).
% 5.19/2.01  tff(c_3350, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2311, c_3349])).
% 5.19/2.01  tff(c_2150, plain, (![A_247]: (m1_subset_1(A_247, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_247), k2_relat_1(A_247)))) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.19/2.01  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.19/2.01  tff(c_2169, plain, (![A_247]: (r1_tarski(A_247, k2_zfmisc_1(k1_relat_1(A_247), k2_relat_1(A_247))) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(resolution, [status(thm)], [c_2150, c_32])).
% 5.19/2.01  tff(c_3397, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3350, c_2169])).
% 5.19/2.01  tff(c_3450, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_68, c_30, c_3397])).
% 5.19/2.01  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.19/2.01  tff(c_218, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.19/2.01  tff(c_239, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_218])).
% 5.19/2.01  tff(c_3486, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3450, c_239])).
% 5.19/2.01  tff(c_3537, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3486, c_8])).
% 5.19/2.01  tff(c_42, plain, (![A_21]: (k9_relat_1(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.19/2.01  tff(c_3534, plain, (![A_21]: (k9_relat_1('#skF_4', A_21)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3486, c_3486, c_42])).
% 5.19/2.01  tff(c_2295, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2288, c_60])).
% 5.19/2.01  tff(c_3783, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_2295])).
% 5.19/2.01  tff(c_3787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3537, c_3783])).
% 5.19/2.01  tff(c_3788, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2310])).
% 5.19/2.01  tff(c_3903, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_3788])).
% 5.19/2.01  tff(c_3907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_3903])).
% 5.19/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.01  
% 5.19/2.01  Inference rules
% 5.19/2.01  ----------------------
% 5.19/2.01  #Ref     : 0
% 5.19/2.01  #Sup     : 813
% 5.19/2.01  #Fact    : 0
% 5.19/2.01  #Define  : 0
% 5.19/2.01  #Split   : 5
% 5.19/2.01  #Chain   : 0
% 5.19/2.01  #Close   : 0
% 5.19/2.01  
% 5.19/2.01  Ordering : KBO
% 5.19/2.01  
% 5.19/2.01  Simplification rules
% 5.19/2.01  ----------------------
% 5.19/2.01  #Subsume      : 72
% 5.19/2.01  #Demod        : 1267
% 5.19/2.01  #Tautology    : 479
% 5.19/2.01  #SimpNegUnit  : 2
% 5.19/2.01  #BackRed      : 118
% 5.19/2.01  
% 5.19/2.01  #Partial instantiations: 0
% 5.19/2.01  #Strategies tried      : 1
% 5.19/2.01  
% 5.19/2.01  Timing (in seconds)
% 5.19/2.01  ----------------------
% 5.19/2.02  Preprocessing        : 0.34
% 5.19/2.02  Parsing              : 0.19
% 5.19/2.02  CNF conversion       : 0.02
% 5.19/2.02  Main loop            : 0.85
% 5.19/2.02  Inferencing          : 0.29
% 5.19/2.02  Reduction            : 0.32
% 5.19/2.02  Demodulation         : 0.24
% 5.19/2.02  BG Simplification    : 0.03
% 5.19/2.02  Subsumption          : 0.15
% 5.19/2.02  Abstraction          : 0.04
% 5.19/2.02  MUC search           : 0.00
% 5.19/2.02  Cooper               : 0.00
% 5.19/2.02  Total                : 1.22
% 5.19/2.02  Index Insertion      : 0.00
% 5.19/2.02  Index Deletion       : 0.00
% 5.19/2.02  Index Matching       : 0.00
% 5.19/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
