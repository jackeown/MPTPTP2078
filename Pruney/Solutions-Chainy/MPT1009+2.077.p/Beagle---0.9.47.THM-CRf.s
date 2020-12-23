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
% DateTime   : Thu Dec  3 10:14:53 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 156 expanded)
%              Number of leaves         :   53 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 276 expanded)
%              Number of equality atoms :   55 (  75 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_98,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_147,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_155,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_147])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_849,plain,(
    ! [C_267,A_268,B_269] :
      ( m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ r1_tarski(k2_relat_1(C_267),B_269)
      | ~ r1_tarski(k1_relat_1(C_267),A_268)
      | ~ v1_relat_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1411,plain,(
    ! [C_316,A_317,B_318] :
      ( r1_tarski(C_316,k2_zfmisc_1(A_317,B_318))
      | ~ r1_tarski(k2_relat_1(C_316),B_318)
      | ~ r1_tarski(k1_relat_1(C_316),A_317)
      | ~ v1_relat_1(C_316) ) ),
    inference(resolution,[status(thm)],[c_849,c_58])).

tff(c_1425,plain,(
    ! [C_316,A_317] :
      ( r1_tarski(C_316,k2_zfmisc_1(A_317,k2_relat_1(C_316)))
      | ~ r1_tarski(k1_relat_1(C_316),A_317)
      | ~ v1_relat_1(C_316) ) ),
    inference(resolution,[status(thm)],[c_6,c_1411])).

tff(c_1434,plain,(
    ! [C_326,A_327] :
      ( r1_tarski(C_326,k2_zfmisc_1(A_327,k2_relat_1(C_326)))
      | ~ r1_tarski(k1_relat_1(C_326),A_327)
      | ~ v1_relat_1(C_326) ) ),
    inference(resolution,[status(thm)],[c_6,c_1411])).

tff(c_60,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_337,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k7_relset_1(A_178,B_179,C_180,D_181) = k9_relat_1(C_180,D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_344,plain,(
    ! [A_178,B_179,A_40,D_181] :
      ( k7_relset_1(A_178,B_179,A_40,D_181) = k9_relat_1(A_40,D_181)
      | ~ r1_tarski(A_40,k2_zfmisc_1(A_178,B_179)) ) ),
    inference(resolution,[status(thm)],[c_60,c_337])).

tff(c_1574,plain,(
    ! [A_349,C_350,D_351] :
      ( k7_relset_1(A_349,k2_relat_1(C_350),C_350,D_351) = k9_relat_1(C_350,D_351)
      | ~ r1_tarski(k1_relat_1(C_350),A_349)
      | ~ v1_relat_1(C_350) ) ),
    inference(resolution,[status(thm)],[c_1434,c_344])).

tff(c_1593,plain,(
    ! [C_354,D_355] :
      ( k7_relset_1(k1_relat_1(C_354),k2_relat_1(C_354),C_354,D_355) = k9_relat_1(C_354,D_355)
      | ~ v1_relat_1(C_354) ) ),
    inference(resolution,[status(thm)],[c_6,c_1574])).

tff(c_373,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( m1_subset_1(k7_relset_1(A_190,B_191,C_192,D_193),k1_zfmisc_1(B_191))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_456,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( r1_tarski(k7_relset_1(A_203,B_204,C_205,D_206),B_204)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(resolution,[status(thm)],[c_373,c_58])).

tff(c_468,plain,(
    ! [A_203,B_204,A_40,D_206] :
      ( r1_tarski(k7_relset_1(A_203,B_204,A_40,D_206),B_204)
      | ~ r1_tarski(A_40,k2_zfmisc_1(A_203,B_204)) ) ),
    inference(resolution,[status(thm)],[c_60,c_456])).

tff(c_1634,plain,(
    ! [C_361,D_362] :
      ( r1_tarski(k9_relat_1(C_361,D_362),k2_relat_1(C_361))
      | ~ r1_tarski(C_361,k2_zfmisc_1(k1_relat_1(C_361),k2_relat_1(C_361)))
      | ~ v1_relat_1(C_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1593,c_468])).

tff(c_1637,plain,(
    ! [C_316,D_362] :
      ( r1_tarski(k9_relat_1(C_316,D_362),k2_relat_1(C_316))
      | ~ r1_tarski(k1_relat_1(C_316),k1_relat_1(C_316))
      | ~ v1_relat_1(C_316) ) ),
    inference(resolution,[status(thm)],[c_1425,c_1634])).

tff(c_1641,plain,(
    ! [C_363,D_364] :
      ( r1_tarski(k9_relat_1(C_363,D_364),k2_relat_1(C_363))
      | ~ v1_relat_1(C_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1637])).

tff(c_102,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_343,plain,(
    ! [D_181] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_181) = k9_relat_1('#skF_6',D_181) ),
    inference(resolution,[status(thm)],[c_98,c_337])).

tff(c_248,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_relset_1(A_149,B_150,C_151) = k2_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_256,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_248])).

tff(c_573,plain,(
    ! [A_227,B_228,C_229] :
      ( k7_relset_1(A_227,B_228,C_229,A_227) = k2_relset_1(A_227,B_228,C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_578,plain,(
    k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',k1_tarski('#skF_3')) = k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_573])).

tff(c_584,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_256,c_578])).

tff(c_62,plain,(
    ! [A_42,B_44] :
      ( k9_relat_1(A_42,k1_tarski(B_44)) = k11_relat_1(A_42,B_44)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_596,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_62])).

tff(c_604,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_596])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_100,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_272,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_280,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_272])).

tff(c_927,plain,(
    ! [B_274,A_275,C_276] :
      ( k1_xboole_0 = B_274
      | k1_relset_1(A_275,B_274,C_276) = A_275
      | ~ v1_funct_2(C_276,A_275,B_274)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_275,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_937,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_927])).

tff(c_946,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_280,c_937])).

tff(c_947,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_946])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_189,plain,(
    ! [A_121,B_122,C_123,D_124] : k3_enumset1(A_121,A_121,B_122,C_123,D_124) = k2_enumset1(A_121,B_122,C_123,D_124) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_31,G_39,C_33,B_32,E_35] : r2_hidden(G_39,k3_enumset1(A_31,B_32,C_33,G_39,E_35)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_213,plain,(
    ! [C_125,A_126,B_127,D_128] : r2_hidden(C_125,k2_enumset1(A_126,B_127,C_125,D_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_26])).

tff(c_217,plain,(
    ! [B_129,A_130,C_131] : r2_hidden(B_129,k1_enumset1(A_130,B_129,C_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_213])).

tff(c_221,plain,(
    ! [A_132,B_133] : r2_hidden(A_132,k2_tarski(A_132,B_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_217])).

tff(c_224,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_221])).

tff(c_964,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_224])).

tff(c_64,plain,(
    ! [B_46,A_45] :
      ( k1_tarski(k1_funct_1(B_46,A_45)) = k11_relat_1(B_46,A_45)
      | ~ r2_hidden(A_45,k1_relat_1(B_46))
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_974,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_964,c_64])).

tff(c_977,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_102,c_604,c_974])).

tff(c_94,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_345,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_94])).

tff(c_1051,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_345])).

tff(c_1644,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1641,c_1051])).

tff(c_1665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.71  
% 4.19/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.71  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.19/1.71  
% 4.19/1.71  %Foreground sorts:
% 4.19/1.71  
% 4.19/1.71  
% 4.19/1.71  %Background operators:
% 4.19/1.71  
% 4.19/1.71  
% 4.19/1.71  %Foreground operators:
% 4.19/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.19/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 4.19/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 4.19/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.19/1.71  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.19/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.19/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.19/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.19/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.19/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.19/1.71  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.19/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.19/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.19/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.19/1.71  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.19/1.71  tff('#skF_6', type, '#skF_6': $i).
% 4.19/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.19/1.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.19/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.19/1.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.19/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.19/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.19/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.19/1.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.19/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.19/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.19/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.19/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.19/1.71  
% 4.19/1.73  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 4.19/1.73  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.19/1.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.19/1.73  tff(f_111, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.19/1.73  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.19/1.73  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.19/1.73  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.19/1.73  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.19/1.73  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.19/1.73  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 4.19/1.73  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.19/1.73  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.19/1.73  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.19/1.73  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.19/1.73  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.19/1.73  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.19/1.73  tff(f_66, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 4.19/1.73  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 4.19/1.73  tff(c_98, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.19/1.73  tff(c_147, plain, (![C_103, A_104, B_105]: (v1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.19/1.73  tff(c_155, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_98, c_147])).
% 4.19/1.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.73  tff(c_849, plain, (![C_267, A_268, B_269]: (m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~r1_tarski(k2_relat_1(C_267), B_269) | ~r1_tarski(k1_relat_1(C_267), A_268) | ~v1_relat_1(C_267))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.19/1.73  tff(c_58, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.19/1.73  tff(c_1411, plain, (![C_316, A_317, B_318]: (r1_tarski(C_316, k2_zfmisc_1(A_317, B_318)) | ~r1_tarski(k2_relat_1(C_316), B_318) | ~r1_tarski(k1_relat_1(C_316), A_317) | ~v1_relat_1(C_316))), inference(resolution, [status(thm)], [c_849, c_58])).
% 4.19/1.73  tff(c_1425, plain, (![C_316, A_317]: (r1_tarski(C_316, k2_zfmisc_1(A_317, k2_relat_1(C_316))) | ~r1_tarski(k1_relat_1(C_316), A_317) | ~v1_relat_1(C_316))), inference(resolution, [status(thm)], [c_6, c_1411])).
% 4.19/1.73  tff(c_1434, plain, (![C_326, A_327]: (r1_tarski(C_326, k2_zfmisc_1(A_327, k2_relat_1(C_326))) | ~r1_tarski(k1_relat_1(C_326), A_327) | ~v1_relat_1(C_326))), inference(resolution, [status(thm)], [c_6, c_1411])).
% 4.19/1.73  tff(c_60, plain, (![A_40, B_41]: (m1_subset_1(A_40, k1_zfmisc_1(B_41)) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.19/1.73  tff(c_337, plain, (![A_178, B_179, C_180, D_181]: (k7_relset_1(A_178, B_179, C_180, D_181)=k9_relat_1(C_180, D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.19/1.73  tff(c_344, plain, (![A_178, B_179, A_40, D_181]: (k7_relset_1(A_178, B_179, A_40, D_181)=k9_relat_1(A_40, D_181) | ~r1_tarski(A_40, k2_zfmisc_1(A_178, B_179)))), inference(resolution, [status(thm)], [c_60, c_337])).
% 4.19/1.73  tff(c_1574, plain, (![A_349, C_350, D_351]: (k7_relset_1(A_349, k2_relat_1(C_350), C_350, D_351)=k9_relat_1(C_350, D_351) | ~r1_tarski(k1_relat_1(C_350), A_349) | ~v1_relat_1(C_350))), inference(resolution, [status(thm)], [c_1434, c_344])).
% 4.19/1.73  tff(c_1593, plain, (![C_354, D_355]: (k7_relset_1(k1_relat_1(C_354), k2_relat_1(C_354), C_354, D_355)=k9_relat_1(C_354, D_355) | ~v1_relat_1(C_354))), inference(resolution, [status(thm)], [c_6, c_1574])).
% 4.19/1.73  tff(c_373, plain, (![A_190, B_191, C_192, D_193]: (m1_subset_1(k7_relset_1(A_190, B_191, C_192, D_193), k1_zfmisc_1(B_191)) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.19/1.73  tff(c_456, plain, (![A_203, B_204, C_205, D_206]: (r1_tarski(k7_relset_1(A_203, B_204, C_205, D_206), B_204) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(resolution, [status(thm)], [c_373, c_58])).
% 4.19/1.73  tff(c_468, plain, (![A_203, B_204, A_40, D_206]: (r1_tarski(k7_relset_1(A_203, B_204, A_40, D_206), B_204) | ~r1_tarski(A_40, k2_zfmisc_1(A_203, B_204)))), inference(resolution, [status(thm)], [c_60, c_456])).
% 4.19/1.73  tff(c_1634, plain, (![C_361, D_362]: (r1_tarski(k9_relat_1(C_361, D_362), k2_relat_1(C_361)) | ~r1_tarski(C_361, k2_zfmisc_1(k1_relat_1(C_361), k2_relat_1(C_361))) | ~v1_relat_1(C_361))), inference(superposition, [status(thm), theory('equality')], [c_1593, c_468])).
% 4.19/1.73  tff(c_1637, plain, (![C_316, D_362]: (r1_tarski(k9_relat_1(C_316, D_362), k2_relat_1(C_316)) | ~r1_tarski(k1_relat_1(C_316), k1_relat_1(C_316)) | ~v1_relat_1(C_316))), inference(resolution, [status(thm)], [c_1425, c_1634])).
% 4.19/1.73  tff(c_1641, plain, (![C_363, D_364]: (r1_tarski(k9_relat_1(C_363, D_364), k2_relat_1(C_363)) | ~v1_relat_1(C_363))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1637])).
% 4.19/1.73  tff(c_102, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.19/1.73  tff(c_343, plain, (![D_181]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_181)=k9_relat_1('#skF_6', D_181))), inference(resolution, [status(thm)], [c_98, c_337])).
% 4.19/1.73  tff(c_248, plain, (![A_149, B_150, C_151]: (k2_relset_1(A_149, B_150, C_151)=k2_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.19/1.73  tff(c_256, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_98, c_248])).
% 4.19/1.73  tff(c_573, plain, (![A_227, B_228, C_229]: (k7_relset_1(A_227, B_228, C_229, A_227)=k2_relset_1(A_227, B_228, C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.19/1.73  tff(c_578, plain, (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', k1_tarski('#skF_3'))=k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_98, c_573])).
% 4.19/1.73  tff(c_584, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_256, c_578])).
% 4.19/1.73  tff(c_62, plain, (![A_42, B_44]: (k9_relat_1(A_42, k1_tarski(B_44))=k11_relat_1(A_42, B_44) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.19/1.73  tff(c_596, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_584, c_62])).
% 4.19/1.73  tff(c_604, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_596])).
% 4.19/1.73  tff(c_96, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.19/1.73  tff(c_100, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.19/1.73  tff(c_272, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.19/1.73  tff(c_280, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_98, c_272])).
% 4.19/1.73  tff(c_927, plain, (![B_274, A_275, C_276]: (k1_xboole_0=B_274 | k1_relset_1(A_275, B_274, C_276)=A_275 | ~v1_funct_2(C_276, A_275, B_274) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_275, B_274))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.19/1.73  tff(c_937, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_98, c_927])).
% 4.19/1.73  tff(c_946, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_280, c_937])).
% 4.19/1.73  tff(c_947, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_96, c_946])).
% 4.19/1.73  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.19/1.73  tff(c_10, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.19/1.73  tff(c_12, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.19/1.73  tff(c_189, plain, (![A_121, B_122, C_123, D_124]: (k3_enumset1(A_121, A_121, B_122, C_123, D_124)=k2_enumset1(A_121, B_122, C_123, D_124))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.19/1.73  tff(c_26, plain, (![A_31, G_39, C_33, B_32, E_35]: (r2_hidden(G_39, k3_enumset1(A_31, B_32, C_33, G_39, E_35)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.19/1.73  tff(c_213, plain, (![C_125, A_126, B_127, D_128]: (r2_hidden(C_125, k2_enumset1(A_126, B_127, C_125, D_128)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_26])).
% 4.19/1.73  tff(c_217, plain, (![B_129, A_130, C_131]: (r2_hidden(B_129, k1_enumset1(A_130, B_129, C_131)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_213])).
% 4.19/1.73  tff(c_221, plain, (![A_132, B_133]: (r2_hidden(A_132, k2_tarski(A_132, B_133)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_217])).
% 4.19/1.73  tff(c_224, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_221])).
% 4.19/1.73  tff(c_964, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_947, c_224])).
% 4.19/1.73  tff(c_64, plain, (![B_46, A_45]: (k1_tarski(k1_funct_1(B_46, A_45))=k11_relat_1(B_46, A_45) | ~r2_hidden(A_45, k1_relat_1(B_46)) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.19/1.73  tff(c_974, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_964, c_64])).
% 4.19/1.73  tff(c_977, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_102, c_604, c_974])).
% 4.19/1.73  tff(c_94, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.19/1.73  tff(c_345, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_94])).
% 4.19/1.73  tff(c_1051, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_977, c_345])).
% 4.19/1.73  tff(c_1644, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1641, c_1051])).
% 4.19/1.73  tff(c_1665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_1644])).
% 4.19/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.73  
% 4.19/1.73  Inference rules
% 4.19/1.73  ----------------------
% 4.19/1.73  #Ref     : 0
% 4.19/1.73  #Sup     : 341
% 4.19/1.73  #Fact    : 0
% 4.19/1.73  #Define  : 0
% 4.19/1.73  #Split   : 4
% 4.19/1.73  #Chain   : 0
% 4.19/1.73  #Close   : 0
% 4.19/1.73  
% 4.19/1.73  Ordering : KBO
% 4.19/1.73  
% 4.19/1.73  Simplification rules
% 4.19/1.73  ----------------------
% 4.19/1.73  #Subsume      : 19
% 4.19/1.73  #Demod        : 165
% 4.19/1.73  #Tautology    : 146
% 4.19/1.73  #SimpNegUnit  : 3
% 4.19/1.73  #BackRed      : 12
% 4.19/1.73  
% 4.19/1.73  #Partial instantiations: 0
% 4.19/1.73  #Strategies tried      : 1
% 4.19/1.73  
% 4.19/1.73  Timing (in seconds)
% 4.19/1.73  ----------------------
% 4.19/1.73  Preprocessing        : 0.39
% 4.19/1.73  Parsing              : 0.20
% 4.19/1.73  CNF conversion       : 0.03
% 4.19/1.73  Main loop            : 0.57
% 4.19/1.73  Inferencing          : 0.21
% 4.19/1.73  Reduction            : 0.18
% 4.19/1.73  Demodulation         : 0.13
% 4.19/1.73  BG Simplification    : 0.03
% 4.19/1.73  Subsumption          : 0.11
% 4.19/1.73  Abstraction          : 0.03
% 4.19/1.73  MUC search           : 0.00
% 4.19/1.73  Cooper               : 0.00
% 4.19/1.73  Total                : 1.00
% 4.19/1.73  Index Insertion      : 0.00
% 4.19/1.73  Index Deletion       : 0.00
% 4.19/1.73  Index Matching       : 0.00
% 4.19/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
