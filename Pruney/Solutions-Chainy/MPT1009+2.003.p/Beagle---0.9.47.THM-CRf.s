%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:42 EST 2020

% Result     : Theorem 6.53s
% Output     : CNFRefutation 6.53s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 344 expanded)
%              Number of leaves         :   52 ( 132 expanded)
%              Depth                    :   12
%              Number of atoms          :  184 ( 730 expanded)
%              Number of equality atoms :   49 ( 155 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_101,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_82,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_100,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_249,plain,(
    ! [C_94,A_95,B_96] :
      ( v1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_289,plain,(
    ! [A_99,A_100,B_101] :
      ( v1_relat_1(A_99)
      | ~ r1_tarski(A_99,k2_zfmisc_1(A_100,B_101)) ) ),
    inference(resolution,[status(thm)],[c_40,c_249])).

tff(c_312,plain,(
    ! [A_100,B_101] : v1_relat_1(k2_zfmisc_1(A_100,B_101)) ),
    inference(resolution,[status(thm)],[c_6,c_289])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_199,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_206,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_199])).

tff(c_208,plain,(
    ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_208])).

tff(c_327,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_62,plain,(
    ! [B_51,A_50] :
      ( r1_tarski(k7_relat_1(B_51,A_50),B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_329,plain,(
    ! [A_105,B_106] :
      ( v1_relat_1(A_105)
      | ~ v1_relat_1(B_106)
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_40,c_199])).

tff(c_345,plain,(
    ! [B_51,A_50] :
      ( v1_relat_1(k7_relat_1(B_51,A_50))
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_62,c_329])).

tff(c_50,plain,(
    ! [B_46,A_45] :
      ( k2_relat_1(k7_relat_1(B_46,A_45)) = k9_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_840,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(k2_relat_1(A_179),k2_relat_1(B_180))
      | ~ r1_tarski(A_179,B_180)
      | ~ v1_relat_1(B_180)
      | ~ v1_relat_1(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6378,plain,(
    ! [B_599,A_600,B_601] :
      ( r1_tarski(k9_relat_1(B_599,A_600),k2_relat_1(B_601))
      | ~ r1_tarski(k7_relat_1(B_599,A_600),B_601)
      | ~ v1_relat_1(B_601)
      | ~ v1_relat_1(k7_relat_1(B_599,A_600))
      | ~ v1_relat_1(B_599) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_840])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_975,plain,(
    ! [B_191,A_192] :
      ( k1_tarski(k1_funct_1(B_191,A_192)) = k2_relat_1(B_191)
      | k1_tarski(A_192) != k1_relat_1(B_191)
      | ~ v1_funct_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_76,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_984,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_76])).

tff(c_990,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_84,c_984])).

tff(c_1031,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_990])).

tff(c_491,plain,(
    ! [C_128,A_129,B_130] :
      ( v4_relat_1(C_128,A_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_505,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_491])).

tff(c_46,plain,(
    ! [B_43,A_42] :
      ( r1_tarski(k1_relat_1(B_43),A_42)
      | ~ v4_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_645,plain,(
    ! [B_152,A_153] :
      ( k1_tarski(B_152) = A_153
      | k1_xboole_0 = A_153
      | ~ r1_tarski(A_153,k1_tarski(B_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3085,plain,(
    ! [B_400,B_401] :
      ( k1_tarski(B_400) = k1_relat_1(B_401)
      | k1_relat_1(B_401) = k1_xboole_0
      | ~ v4_relat_1(B_401,k1_tarski(B_400))
      | ~ v1_relat_1(B_401) ) ),
    inference(resolution,[status(thm)],[c_46,c_645])).

tff(c_3123,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_505,c_3085])).

tff(c_3142,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_3123])).

tff(c_3143,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1031,c_3142])).

tff(c_36,plain,(
    ! [B_36] : k2_zfmisc_1(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1259,plain,(
    ! [D_234,B_235,C_236,A_237] :
      ( m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(B_235,C_236)))
      | ~ r1_tarski(k1_relat_1(D_234),B_235)
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(A_237,C_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1272,plain,(
    ! [B_238] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_238,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_238) ) ),
    inference(resolution,[status(thm)],[c_80,c_1259])).

tff(c_1295,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1272])).

tff(c_1339,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1295])).

tff(c_3155,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3143,c_1339])).

tff(c_3167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3155])).

tff(c_3168,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3190,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3168,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3256,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_3190,c_2])).

tff(c_3274,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3256])).

tff(c_3312,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3274,c_8])).

tff(c_60,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    ! [A_44] : v1_relat_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_93,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_56,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_159,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k7_relat_1(B_79,A_80),B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_163,plain,(
    ! [A_80] :
      ( k7_relat_1(k1_xboole_0,A_80) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_159,c_10])).

tff(c_166,plain,(
    ! [A_80] : k7_relat_1(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_163])).

tff(c_518,plain,(
    ! [B_133,A_134] :
      ( k2_relat_1(k7_relat_1(B_133,A_134)) = k9_relat_1(B_133,A_134)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_527,plain,(
    ! [A_80] :
      ( k9_relat_1(k1_xboole_0,A_80) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_518])).

tff(c_531,plain,(
    ! [A_80] : k9_relat_1(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_56,c_527])).

tff(c_3298,plain,(
    ! [A_80] : k9_relat_1('#skF_4',A_80) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3274,c_3274,c_531])).

tff(c_1095,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( k7_relset_1(A_208,B_209,C_210,D_211) = k9_relat_1(C_210,D_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1105,plain,(
    ! [D_211] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_211) = k9_relat_1('#skF_4',D_211) ),
    inference(resolution,[status(thm)],[c_80,c_1095])).

tff(c_1145,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1105,c_76])).

tff(c_3659,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_1145])).

tff(c_3662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3312,c_3659])).

tff(c_3664,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_990])).

tff(c_3665,plain,(
    ! [A_421,B_422,C_423,D_424] :
      ( k7_relset_1(A_421,B_422,C_423,D_424) = k9_relat_1(C_423,D_424)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_421,B_422))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3675,plain,(
    ! [D_424] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_424) = k9_relat_1('#skF_4',D_424) ),
    inference(resolution,[status(thm)],[c_80,c_3665])).

tff(c_3788,plain,(
    ! [D_424] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_424) = k9_relat_1('#skF_4',D_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3664,c_3675])).

tff(c_3663,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_990])).

tff(c_3787,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3664,c_3663])).

tff(c_3789,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3788,c_3787])).

tff(c_6381,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6378,c_3789])).

tff(c_6407,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_6381])).

tff(c_6414,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6407])).

tff(c_6417,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_345,c_6414])).

tff(c_6421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_6417])).

tff(c_6422,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6407])).

tff(c_6426,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_6422])).

tff(c_6430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_6426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.53/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.34  
% 6.53/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.53/2.34  
% 6.53/2.34  %Foreground sorts:
% 6.53/2.34  
% 6.53/2.34  
% 6.53/2.34  %Background operators:
% 6.53/2.34  
% 6.53/2.34  
% 6.53/2.34  %Foreground operators:
% 6.53/2.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.53/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.53/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.53/2.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.53/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.53/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.53/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.53/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.53/2.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.53/2.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.53/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.53/2.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.53/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.53/2.34  tff('#skF_2', type, '#skF_2': $i).
% 6.53/2.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.53/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.53/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.53/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.53/2.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.53/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.53/2.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.53/2.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.53/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.53/2.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.53/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.53/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.53/2.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.53/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.53/2.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.53/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.53/2.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.53/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.53/2.34  
% 6.53/2.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.53/2.36  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.53/2.36  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.53/2.36  tff(f_145, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 6.53/2.36  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.53/2.36  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 6.53/2.36  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.53/2.36  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 6.53/2.36  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.53/2.36  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 6.53/2.36  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.53/2.36  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 6.53/2.36  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.53/2.36  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.53/2.36  tff(f_133, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 6.53/2.36  tff(f_101, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.53/2.36  tff(f_82, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.53/2.36  tff(f_100, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.53/2.36  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.53/2.36  tff(f_127, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.53/2.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.53/2.36  tff(c_40, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.53/2.36  tff(c_249, plain, (![C_94, A_95, B_96]: (v1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.53/2.36  tff(c_289, plain, (![A_99, A_100, B_101]: (v1_relat_1(A_99) | ~r1_tarski(A_99, k2_zfmisc_1(A_100, B_101)))), inference(resolution, [status(thm)], [c_40, c_249])).
% 6.53/2.36  tff(c_312, plain, (![A_100, B_101]: (v1_relat_1(k2_zfmisc_1(A_100, B_101)))), inference(resolution, [status(thm)], [c_6, c_289])).
% 6.53/2.36  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.53/2.36  tff(c_199, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.53/2.36  tff(c_206, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_199])).
% 6.53/2.36  tff(c_208, plain, (~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_206])).
% 6.53/2.36  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_312, c_208])).
% 6.53/2.36  tff(c_327, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_206])).
% 6.53/2.36  tff(c_62, plain, (![B_51, A_50]: (r1_tarski(k7_relat_1(B_51, A_50), B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.53/2.36  tff(c_329, plain, (![A_105, B_106]: (v1_relat_1(A_105) | ~v1_relat_1(B_106) | ~r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_40, c_199])).
% 6.53/2.36  tff(c_345, plain, (![B_51, A_50]: (v1_relat_1(k7_relat_1(B_51, A_50)) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_62, c_329])).
% 6.53/2.36  tff(c_50, plain, (![B_46, A_45]: (k2_relat_1(k7_relat_1(B_46, A_45))=k9_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.53/2.36  tff(c_840, plain, (![A_179, B_180]: (r1_tarski(k2_relat_1(A_179), k2_relat_1(B_180)) | ~r1_tarski(A_179, B_180) | ~v1_relat_1(B_180) | ~v1_relat_1(A_179))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.53/2.36  tff(c_6378, plain, (![B_599, A_600, B_601]: (r1_tarski(k9_relat_1(B_599, A_600), k2_relat_1(B_601)) | ~r1_tarski(k7_relat_1(B_599, A_600), B_601) | ~v1_relat_1(B_601) | ~v1_relat_1(k7_relat_1(B_599, A_600)) | ~v1_relat_1(B_599))), inference(superposition, [status(thm), theory('equality')], [c_50, c_840])).
% 6.53/2.36  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.53/2.36  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.53/2.36  tff(c_975, plain, (![B_191, A_192]: (k1_tarski(k1_funct_1(B_191, A_192))=k2_relat_1(B_191) | k1_tarski(A_192)!=k1_relat_1(B_191) | ~v1_funct_1(B_191) | ~v1_relat_1(B_191))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.53/2.36  tff(c_76, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.53/2.36  tff(c_984, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_975, c_76])).
% 6.53/2.36  tff(c_990, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_84, c_984])).
% 6.53/2.36  tff(c_1031, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_990])).
% 6.53/2.36  tff(c_491, plain, (![C_128, A_129, B_130]: (v4_relat_1(C_128, A_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.53/2.36  tff(c_505, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_491])).
% 6.53/2.36  tff(c_46, plain, (![B_43, A_42]: (r1_tarski(k1_relat_1(B_43), A_42) | ~v4_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.53/2.36  tff(c_645, plain, (![B_152, A_153]: (k1_tarski(B_152)=A_153 | k1_xboole_0=A_153 | ~r1_tarski(A_153, k1_tarski(B_152)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.53/2.36  tff(c_3085, plain, (![B_400, B_401]: (k1_tarski(B_400)=k1_relat_1(B_401) | k1_relat_1(B_401)=k1_xboole_0 | ~v4_relat_1(B_401, k1_tarski(B_400)) | ~v1_relat_1(B_401))), inference(resolution, [status(thm)], [c_46, c_645])).
% 6.53/2.36  tff(c_3123, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_505, c_3085])).
% 6.53/2.36  tff(c_3142, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_327, c_3123])).
% 6.53/2.36  tff(c_3143, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1031, c_3142])).
% 6.53/2.36  tff(c_36, plain, (![B_36]: (k2_zfmisc_1(k1_xboole_0, B_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.53/2.36  tff(c_1259, plain, (![D_234, B_235, C_236, A_237]: (m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(B_235, C_236))) | ~r1_tarski(k1_relat_1(D_234), B_235) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(A_237, C_236))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.53/2.36  tff(c_1272, plain, (![B_238]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_238, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_238))), inference(resolution, [status(thm)], [c_80, c_1259])).
% 6.53/2.36  tff(c_1295, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_1272])).
% 6.53/2.36  tff(c_1339, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1295])).
% 6.53/2.36  tff(c_3155, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3143, c_1339])).
% 6.53/2.36  tff(c_3167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3155])).
% 6.53/2.36  tff(c_3168, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1295])).
% 6.53/2.36  tff(c_38, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.53/2.36  tff(c_3190, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_3168, c_38])).
% 6.53/2.36  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.53/2.36  tff(c_3256, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_3190, c_2])).
% 6.53/2.36  tff(c_3274, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3256])).
% 6.53/2.36  tff(c_3312, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3274, c_8])).
% 6.53/2.36  tff(c_60, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.53/2.36  tff(c_48, plain, (![A_44]: (v1_relat_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.53/2.36  tff(c_93, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_48])).
% 6.53/2.36  tff(c_56, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.53/2.36  tff(c_159, plain, (![B_79, A_80]: (r1_tarski(k7_relat_1(B_79, A_80), B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.53/2.36  tff(c_10, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.53/2.36  tff(c_163, plain, (![A_80]: (k7_relat_1(k1_xboole_0, A_80)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_159, c_10])).
% 6.53/2.36  tff(c_166, plain, (![A_80]: (k7_relat_1(k1_xboole_0, A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_163])).
% 6.53/2.36  tff(c_518, plain, (![B_133, A_134]: (k2_relat_1(k7_relat_1(B_133, A_134))=k9_relat_1(B_133, A_134) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.53/2.36  tff(c_527, plain, (![A_80]: (k9_relat_1(k1_xboole_0, A_80)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_166, c_518])).
% 6.53/2.36  tff(c_531, plain, (![A_80]: (k9_relat_1(k1_xboole_0, A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_56, c_527])).
% 6.53/2.36  tff(c_3298, plain, (![A_80]: (k9_relat_1('#skF_4', A_80)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3274, c_3274, c_531])).
% 6.53/2.36  tff(c_1095, plain, (![A_208, B_209, C_210, D_211]: (k7_relset_1(A_208, B_209, C_210, D_211)=k9_relat_1(C_210, D_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.53/2.36  tff(c_1105, plain, (![D_211]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_211)=k9_relat_1('#skF_4', D_211))), inference(resolution, [status(thm)], [c_80, c_1095])).
% 6.53/2.36  tff(c_1145, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1105, c_76])).
% 6.53/2.36  tff(c_3659, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_1145])).
% 6.53/2.36  tff(c_3662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3312, c_3659])).
% 6.53/2.36  tff(c_3664, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_990])).
% 6.53/2.36  tff(c_3665, plain, (![A_421, B_422, C_423, D_424]: (k7_relset_1(A_421, B_422, C_423, D_424)=k9_relat_1(C_423, D_424) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_421, B_422))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.53/2.36  tff(c_3675, plain, (![D_424]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_424)=k9_relat_1('#skF_4', D_424))), inference(resolution, [status(thm)], [c_80, c_3665])).
% 6.53/2.36  tff(c_3788, plain, (![D_424]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_424)=k9_relat_1('#skF_4', D_424))), inference(demodulation, [status(thm), theory('equality')], [c_3664, c_3675])).
% 6.53/2.36  tff(c_3663, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_990])).
% 6.53/2.36  tff(c_3787, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3664, c_3663])).
% 6.53/2.36  tff(c_3789, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3788, c_3787])).
% 6.53/2.36  tff(c_6381, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6378, c_3789])).
% 6.53/2.36  tff(c_6407, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_6381])).
% 6.53/2.36  tff(c_6414, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6407])).
% 6.53/2.36  tff(c_6417, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_345, c_6414])).
% 6.53/2.36  tff(c_6421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_6417])).
% 6.53/2.36  tff(c_6422, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_6407])).
% 6.53/2.36  tff(c_6426, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_6422])).
% 6.53/2.36  tff(c_6430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_6426])).
% 6.53/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.36  
% 6.53/2.36  Inference rules
% 6.53/2.36  ----------------------
% 6.53/2.36  #Ref     : 0
% 6.53/2.36  #Sup     : 1324
% 6.53/2.36  #Fact    : 0
% 6.53/2.36  #Define  : 0
% 6.53/2.36  #Split   : 11
% 6.53/2.36  #Chain   : 0
% 6.53/2.36  #Close   : 0
% 6.53/2.36  
% 6.53/2.36  Ordering : KBO
% 6.53/2.36  
% 6.53/2.36  Simplification rules
% 6.53/2.36  ----------------------
% 6.53/2.36  #Subsume      : 268
% 6.53/2.36  #Demod        : 1523
% 6.53/2.36  #Tautology    : 579
% 6.53/2.36  #SimpNegUnit  : 28
% 6.53/2.36  #BackRed      : 103
% 6.53/2.36  
% 6.53/2.36  #Partial instantiations: 0
% 6.53/2.36  #Strategies tried      : 1
% 6.53/2.36  
% 6.53/2.36  Timing (in seconds)
% 6.53/2.36  ----------------------
% 6.53/2.37  Preprocessing        : 0.35
% 6.53/2.37  Parsing              : 0.18
% 6.53/2.37  CNF conversion       : 0.03
% 6.53/2.37  Main loop            : 1.17
% 6.53/2.37  Inferencing          : 0.39
% 6.53/2.37  Reduction            : 0.43
% 6.53/2.37  Demodulation         : 0.31
% 6.53/2.37  BG Simplification    : 0.04
% 6.53/2.37  Subsumption          : 0.22
% 6.53/2.37  Abstraction          : 0.05
% 6.53/2.37  MUC search           : 0.00
% 6.53/2.37  Cooper               : 0.00
% 6.53/2.37  Total                : 1.56
% 6.53/2.37  Index Insertion      : 0.00
% 6.53/2.37  Index Deletion       : 0.00
% 6.53/2.37  Index Matching       : 0.00
% 6.53/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
