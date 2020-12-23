%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:47 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 480 expanded)
%              Number of leaves         :   46 ( 187 expanded)
%              Depth                    :   17
%              Number of atoms          :  324 (1863 expanded)
%              Number of equality atoms :   66 ( 365 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_198,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_173,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_154,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_72,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_82,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_80,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_74,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_293,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_306,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_293])).

tff(c_70,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_310,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_70])).

tff(c_76,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1274,plain,(
    ! [D_257,E_256,B_255,A_254,C_258,F_259] :
      ( k1_funct_1(k8_funct_2(B_255,C_258,A_254,D_257,E_256),F_259) = k1_funct_1(E_256,k1_funct_1(D_257,F_259))
      | k1_xboole_0 = B_255
      | ~ r1_tarski(k2_relset_1(B_255,C_258,D_257),k1_relset_1(C_258,A_254,E_256))
      | ~ m1_subset_1(F_259,B_255)
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(C_258,A_254)))
      | ~ v1_funct_1(E_256)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(B_255,C_258)))
      | ~ v1_funct_2(D_257,B_255,C_258)
      | ~ v1_funct_1(D_257)
      | v1_xboole_0(C_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1280,plain,(
    ! [B_255,D_257,F_259] :
      ( k1_funct_1(k8_funct_2(B_255,'#skF_5','#skF_3',D_257,'#skF_7'),F_259) = k1_funct_1('#skF_7',k1_funct_1(D_257,F_259))
      | k1_xboole_0 = B_255
      | ~ r1_tarski(k2_relset_1(B_255,'#skF_5',D_257),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_259,B_255)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(B_255,'#skF_5')))
      | ~ v1_funct_2(D_257,B_255,'#skF_5')
      | ~ v1_funct_1(D_257)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_1274])).

tff(c_1289,plain,(
    ! [B_255,D_257,F_259] :
      ( k1_funct_1(k8_funct_2(B_255,'#skF_5','#skF_3',D_257,'#skF_7'),F_259) = k1_funct_1('#skF_7',k1_funct_1(D_257,F_259))
      | k1_xboole_0 = B_255
      | ~ r1_tarski(k2_relset_1(B_255,'#skF_5',D_257),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_259,B_255)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(B_255,'#skF_5')))
      | ~ v1_funct_2(D_257,B_255,'#skF_5')
      | ~ v1_funct_1(D_257)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1280])).

tff(c_1328,plain,(
    ! [B_266,D_267,F_268] :
      ( k1_funct_1(k8_funct_2(B_266,'#skF_5','#skF_3',D_267,'#skF_7'),F_268) = k1_funct_1('#skF_7',k1_funct_1(D_267,F_268))
      | k1_xboole_0 = B_266
      | ~ r1_tarski(k2_relset_1(B_266,'#skF_5',D_267),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_268,B_266)
      | ~ m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(B_266,'#skF_5')))
      | ~ v1_funct_2(D_267,B_266,'#skF_5')
      | ~ v1_funct_1(D_267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1289])).

tff(c_1330,plain,(
    ! [F_268] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_268) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_268))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_268,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_310,c_1328])).

tff(c_1336,plain,(
    ! [F_268] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_268) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_268))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_268,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1330])).

tff(c_1337,plain,(
    ! [F_268] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_268) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_268))
      | ~ m1_subset_1(F_268,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1336])).

tff(c_234,plain,(
    ! [C_108,B_109,A_110] :
      ( v5_relat_1(C_108,B_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_247,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_234])).

tff(c_32,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_129,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_129])).

tff(c_138,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_132])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1194,plain,(
    ! [B_247,D_248,A_249,C_250] :
      ( k1_xboole_0 = B_247
      | m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_249,C_250)))
      | ~ r1_tarski(k2_relset_1(A_249,B_247,D_248),C_250)
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_2(D_248,A_249,B_247)
      | ~ v1_funct_1(D_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1392,plain,(
    ! [B_276,D_277,A_278] :
      ( k1_xboole_0 = B_276
      | m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(A_278,k2_relset_1(A_278,B_276,D_277))))
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_276)))
      | ~ v1_funct_2(D_277,A_278,B_276)
      | ~ v1_funct_1(D_277) ) ),
    inference(resolution,[status(thm)],[c_18,c_1194])).

tff(c_36,plain,(
    ! [C_27,B_26,A_25] :
      ( v5_relat_1(C_27,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1487,plain,(
    ! [D_288,A_289,B_290] :
      ( v5_relat_1(D_288,k2_relset_1(A_289,B_290,D_288))
      | k1_xboole_0 = B_290
      | ~ m1_subset_1(D_288,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_2(D_288,A_289,B_290)
      | ~ v1_funct_1(D_288) ) ),
    inference(resolution,[status(thm)],[c_1392,c_36])).

tff(c_1497,plain,
    ( v5_relat_1('#skF_6',k2_relset_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_1487])).

tff(c_1509,plain,
    ( v5_relat_1('#skF_6',k2_relset_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1497])).

tff(c_1510,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1509])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1556,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_12])).

tff(c_1559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1556])).

tff(c_1561,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1509])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_999,plain,(
    ! [D_217,C_218,B_219,A_220] :
      ( r2_hidden(k1_funct_1(D_217,C_218),B_219)
      | k1_xboole_0 = B_219
      | ~ r2_hidden(C_218,A_220)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219)))
      | ~ v1_funct_2(D_217,A_220,B_219)
      | ~ v1_funct_1(D_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1700,plain,(
    ! [D_312,A_313,B_314,B_315] :
      ( r2_hidden(k1_funct_1(D_312,A_313),B_314)
      | k1_xboole_0 = B_314
      | ~ m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(B_315,B_314)))
      | ~ v1_funct_2(D_312,B_315,B_314)
      | ~ v1_funct_1(D_312)
      | v1_xboole_0(B_315)
      | ~ m1_subset_1(A_313,B_315) ) ),
    inference(resolution,[status(thm)],[c_28,c_999])).

tff(c_1710,plain,(
    ! [A_313] :
      ( r2_hidden(k1_funct_1('#skF_6',A_313),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_313,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_1700])).

tff(c_1725,plain,(
    ! [A_313] :
      ( r2_hidden(k1_funct_1('#skF_6',A_313),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_313,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1710])).

tff(c_1726,plain,(
    ! [A_313] :
      ( r2_hidden(k1_funct_1('#skF_6',A_313),'#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_313,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1561,c_1725])).

tff(c_1744,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1726])).

tff(c_152,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_2'(A_90,B_91),A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [A_90,B_91] :
      ( ~ v1_xboole_0(A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_164,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | ~ v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_162,c_164])).

tff(c_191,plain,(
    ! [B_98,A_99] :
      ( B_98 = A_99
      | ~ v1_xboole_0(B_98)
      | ~ v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_162,c_177])).

tff(c_194,plain,(
    ! [A_99] :
      ( k1_xboole_0 = A_99
      | ~ v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_12,c_191])).

tff(c_1748,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1744,c_194])).

tff(c_1757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1748])).

tff(c_1759,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1726])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1090,plain,(
    ! [B_234,D_235,A_236,C_237] :
      ( k1_xboole_0 = B_234
      | v1_funct_2(D_235,A_236,C_237)
      | ~ r1_tarski(k2_relset_1(A_236,B_234,D_235),C_237)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_234)))
      | ~ v1_funct_2(D_235,A_236,B_234)
      | ~ v1_funct_1(D_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1092,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_310,c_1090])).

tff(c_1101,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1092])).

tff(c_1122,plain,(
    v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1101])).

tff(c_1196,plain,
    ( k1_xboole_0 = '#skF_5'
    | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_310,c_1194])).

tff(c_1205,plain,
    ( k1_xboole_0 = '#skF_5'
    | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1196])).

tff(c_1208,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ),
    inference(splitLeft,[status(thm)],[c_1205])).

tff(c_1491,plain,
    ( v5_relat_1('#skF_6',k2_relset_1('#skF_4',k1_relat_1('#skF_7'),'#skF_6'))
    | k1_relat_1('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1208,c_1487])).

tff(c_1503,plain,
    ( v5_relat_1('#skF_6',k2_relset_1('#skF_4',k1_relat_1('#skF_7'),'#skF_6'))
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1122,c_1491])).

tff(c_1567,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1503])).

tff(c_347,plain,(
    ! [C_135,A_136,B_137] :
      ( ~ v1_xboole_0(C_135)
      | ~ v1_funct_2(C_135,A_136,B_137)
      | ~ v1_funct_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | v1_xboole_0(B_137)
      | v1_xboole_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_356,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_347])).

tff(c_367,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_356])).

tff(c_368,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_367])).

tff(c_370,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_26,plain,(
    ! [B_16,A_14] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1223,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1208,c_26])).

tff(c_1238,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_1223])).

tff(c_1572,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_1238])).

tff(c_1595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22,c_1572])).

tff(c_1597,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1503])).

tff(c_1704,plain,(
    ! [A_313] :
      ( r2_hidden(k1_funct_1('#skF_6',A_313),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | ~ v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_313,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1208,c_1700])).

tff(c_1716,plain,(
    ! [A_313] :
      ( r2_hidden(k1_funct_1('#skF_6',A_313),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_313,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1122,c_1704])).

tff(c_1717,plain,(
    ! [A_313] :
      ( r2_hidden(k1_funct_1('#skF_6',A_313),k1_relat_1('#skF_7'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_313,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1597,c_1716])).

tff(c_1833,plain,(
    ! [A_324] :
      ( r2_hidden(k1_funct_1('#skF_6',A_324),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(A_324,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1759,c_1717])).

tff(c_48,plain,(
    ! [A_35,B_36,C_38] :
      ( k7_partfun1(A_35,B_36,C_38) = k1_funct_1(B_36,C_38)
      | ~ r2_hidden(C_38,k1_relat_1(B_36))
      | ~ v1_funct_1(B_36)
      | ~ v5_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1837,plain,(
    ! [A_35,A_324] :
      ( k7_partfun1(A_35,'#skF_7',k1_funct_1('#skF_6',A_324)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_324))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_35)
      | ~ v1_relat_1('#skF_7')
      | ~ m1_subset_1(A_324,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1833,c_48])).

tff(c_1889,plain,(
    ! [A_333,A_334] :
      ( k7_partfun1(A_333,'#skF_7',k1_funct_1('#skF_6',A_334)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_334))
      | ~ v5_relat_1('#skF_7',A_333)
      | ~ m1_subset_1(A_334,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_76,c_1837])).

tff(c_66,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1895,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_66])).

tff(c_1901,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_247,c_1895])).

tff(c_1923,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1337,c_1901])).

tff(c_1927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1923])).

tff(c_1928,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1205])).

tff(c_1953,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_12])).

tff(c_1956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1953])).

tff(c_1957,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_1977,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_12])).

tff(c_1980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1977])).

tff(c_1981,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_1986,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1981,c_194])).

tff(c_1995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:42:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.85  
% 4.93/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 4.93/1.85  
% 4.93/1.85  %Foreground sorts:
% 4.93/1.85  
% 4.93/1.85  
% 4.93/1.85  %Background operators:
% 4.93/1.85  
% 4.93/1.85  
% 4.93/1.85  %Foreground operators:
% 4.93/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.93/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.93/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.93/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.93/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.93/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.93/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.93/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.93/1.85  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.93/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.93/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.93/1.85  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.93/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.93/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.93/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.93/1.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.93/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.93/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.93/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.93/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.93/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.93/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.93/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.93/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.93/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.93/1.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.93/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.93/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.93/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.93/1.85  
% 4.93/1.87  tff(f_198, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 4.93/1.87  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.93/1.87  tff(f_142, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 4.93/1.87  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.93/1.87  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.93/1.87  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.93/1.87  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.93/1.87  tff(f_173, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 4.93/1.87  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.93/1.87  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.93/1.87  tff(f_154, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.93/1.87  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.93/1.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.93/1.87  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.93/1.87  tff(f_107, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 4.93/1.87  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.93/1.87  tff(f_118, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 4.93/1.87  tff(c_68, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_84, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_72, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_82, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_80, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_74, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_293, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.93/1.87  tff(c_306, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_74, c_293])).
% 4.93/1.87  tff(c_70, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_310, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_70])).
% 4.93/1.87  tff(c_76, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_1274, plain, (![D_257, E_256, B_255, A_254, C_258, F_259]: (k1_funct_1(k8_funct_2(B_255, C_258, A_254, D_257, E_256), F_259)=k1_funct_1(E_256, k1_funct_1(D_257, F_259)) | k1_xboole_0=B_255 | ~r1_tarski(k2_relset_1(B_255, C_258, D_257), k1_relset_1(C_258, A_254, E_256)) | ~m1_subset_1(F_259, B_255) | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(C_258, A_254))) | ~v1_funct_1(E_256) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(B_255, C_258))) | ~v1_funct_2(D_257, B_255, C_258) | ~v1_funct_1(D_257) | v1_xboole_0(C_258))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.93/1.87  tff(c_1280, plain, (![B_255, D_257, F_259]: (k1_funct_1(k8_funct_2(B_255, '#skF_5', '#skF_3', D_257, '#skF_7'), F_259)=k1_funct_1('#skF_7', k1_funct_1(D_257, F_259)) | k1_xboole_0=B_255 | ~r1_tarski(k2_relset_1(B_255, '#skF_5', D_257), k1_relat_1('#skF_7')) | ~m1_subset_1(F_259, B_255) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(B_255, '#skF_5'))) | ~v1_funct_2(D_257, B_255, '#skF_5') | ~v1_funct_1(D_257) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_1274])).
% 4.93/1.87  tff(c_1289, plain, (![B_255, D_257, F_259]: (k1_funct_1(k8_funct_2(B_255, '#skF_5', '#skF_3', D_257, '#skF_7'), F_259)=k1_funct_1('#skF_7', k1_funct_1(D_257, F_259)) | k1_xboole_0=B_255 | ~r1_tarski(k2_relset_1(B_255, '#skF_5', D_257), k1_relat_1('#skF_7')) | ~m1_subset_1(F_259, B_255) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(B_255, '#skF_5'))) | ~v1_funct_2(D_257, B_255, '#skF_5') | ~v1_funct_1(D_257) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1280])).
% 4.93/1.87  tff(c_1328, plain, (![B_266, D_267, F_268]: (k1_funct_1(k8_funct_2(B_266, '#skF_5', '#skF_3', D_267, '#skF_7'), F_268)=k1_funct_1('#skF_7', k1_funct_1(D_267, F_268)) | k1_xboole_0=B_266 | ~r1_tarski(k2_relset_1(B_266, '#skF_5', D_267), k1_relat_1('#skF_7')) | ~m1_subset_1(F_268, B_266) | ~m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(B_266, '#skF_5'))) | ~v1_funct_2(D_267, B_266, '#skF_5') | ~v1_funct_1(D_267))), inference(negUnitSimplification, [status(thm)], [c_84, c_1289])).
% 4.93/1.87  tff(c_1330, plain, (![F_268]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_268)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_268)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_268, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_310, c_1328])).
% 4.93/1.87  tff(c_1336, plain, (![F_268]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_268)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_268)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_268, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1330])).
% 4.93/1.87  tff(c_1337, plain, (![F_268]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_268)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_268)) | ~m1_subset_1(F_268, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1336])).
% 4.93/1.87  tff(c_234, plain, (![C_108, B_109, A_110]: (v5_relat_1(C_108, B_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.93/1.87  tff(c_247, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_234])).
% 4.93/1.87  tff(c_32, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.93/1.87  tff(c_129, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.93/1.87  tff(c_132, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_129])).
% 4.93/1.87  tff(c_138, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_132])).
% 4.93/1.87  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.93/1.87  tff(c_1194, plain, (![B_247, D_248, A_249, C_250]: (k1_xboole_0=B_247 | m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_249, C_250))) | ~r1_tarski(k2_relset_1(A_249, B_247, D_248), C_250) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_2(D_248, A_249, B_247) | ~v1_funct_1(D_248))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.93/1.87  tff(c_1392, plain, (![B_276, D_277, A_278]: (k1_xboole_0=B_276 | m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(A_278, k2_relset_1(A_278, B_276, D_277)))) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_276))) | ~v1_funct_2(D_277, A_278, B_276) | ~v1_funct_1(D_277))), inference(resolution, [status(thm)], [c_18, c_1194])).
% 4.93/1.87  tff(c_36, plain, (![C_27, B_26, A_25]: (v5_relat_1(C_27, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.93/1.87  tff(c_1487, plain, (![D_288, A_289, B_290]: (v5_relat_1(D_288, k2_relset_1(A_289, B_290, D_288)) | k1_xboole_0=B_290 | ~m1_subset_1(D_288, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_2(D_288, A_289, B_290) | ~v1_funct_1(D_288))), inference(resolution, [status(thm)], [c_1392, c_36])).
% 4.93/1.87  tff(c_1497, plain, (v5_relat_1('#skF_6', k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_1487])).
% 4.93/1.87  tff(c_1509, plain, (v5_relat_1('#skF_6', k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1497])).
% 4.93/1.87  tff(c_1510, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1509])).
% 4.93/1.87  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.93/1.87  tff(c_1556, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_12])).
% 4.93/1.87  tff(c_1559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1556])).
% 4.93/1.87  tff(c_1561, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_1509])).
% 4.93/1.87  tff(c_28, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.93/1.87  tff(c_999, plain, (![D_217, C_218, B_219, A_220]: (r2_hidden(k1_funct_1(D_217, C_218), B_219) | k1_xboole_0=B_219 | ~r2_hidden(C_218, A_220) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))) | ~v1_funct_2(D_217, A_220, B_219) | ~v1_funct_1(D_217))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.93/1.87  tff(c_1700, plain, (![D_312, A_313, B_314, B_315]: (r2_hidden(k1_funct_1(D_312, A_313), B_314) | k1_xboole_0=B_314 | ~m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(B_315, B_314))) | ~v1_funct_2(D_312, B_315, B_314) | ~v1_funct_1(D_312) | v1_xboole_0(B_315) | ~m1_subset_1(A_313, B_315))), inference(resolution, [status(thm)], [c_28, c_999])).
% 4.93/1.87  tff(c_1710, plain, (![A_313]: (r2_hidden(k1_funct_1('#skF_6', A_313), '#skF_5') | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_313, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_1700])).
% 4.93/1.87  tff(c_1725, plain, (![A_313]: (r2_hidden(k1_funct_1('#skF_6', A_313), '#skF_5') | k1_xboole_0='#skF_5' | v1_xboole_0('#skF_4') | ~m1_subset_1(A_313, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1710])).
% 4.93/1.87  tff(c_1726, plain, (![A_313]: (r2_hidden(k1_funct_1('#skF_6', A_313), '#skF_5') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_313, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1561, c_1725])).
% 4.93/1.87  tff(c_1744, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1726])).
% 4.93/1.87  tff(c_152, plain, (![A_90, B_91]: (r2_hidden('#skF_2'(A_90, B_91), A_90) | r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.93/1.87  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.93/1.87  tff(c_162, plain, (![A_90, B_91]: (~v1_xboole_0(A_90) | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_152, c_2])).
% 4.93/1.87  tff(c_164, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.93/1.87  tff(c_177, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | ~v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_162, c_164])).
% 4.93/1.87  tff(c_191, plain, (![B_98, A_99]: (B_98=A_99 | ~v1_xboole_0(B_98) | ~v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_162, c_177])).
% 4.93/1.87  tff(c_194, plain, (![A_99]: (k1_xboole_0=A_99 | ~v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_12, c_191])).
% 4.93/1.87  tff(c_1748, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1744, c_194])).
% 4.93/1.87  tff(c_1757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1748])).
% 4.93/1.87  tff(c_1759, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1726])).
% 4.93/1.87  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.93/1.87  tff(c_1090, plain, (![B_234, D_235, A_236, C_237]: (k1_xboole_0=B_234 | v1_funct_2(D_235, A_236, C_237) | ~r1_tarski(k2_relset_1(A_236, B_234, D_235), C_237) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_234))) | ~v1_funct_2(D_235, A_236, B_234) | ~v1_funct_1(D_235))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.93/1.87  tff(c_1092, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_310, c_1090])).
% 4.93/1.87  tff(c_1101, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1092])).
% 4.93/1.87  tff(c_1122, plain, (v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1101])).
% 4.93/1.87  tff(c_1196, plain, (k1_xboole_0='#skF_5' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_310, c_1194])).
% 4.93/1.87  tff(c_1205, plain, (k1_xboole_0='#skF_5' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1196])).
% 4.93/1.87  tff(c_1208, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7'))))), inference(splitLeft, [status(thm)], [c_1205])).
% 4.93/1.87  tff(c_1491, plain, (v5_relat_1('#skF_6', k2_relset_1('#skF_4', k1_relat_1('#skF_7'), '#skF_6')) | k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_1208, c_1487])).
% 4.93/1.87  tff(c_1503, plain, (v5_relat_1('#skF_6', k2_relset_1('#skF_4', k1_relat_1('#skF_7'), '#skF_6')) | k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1122, c_1491])).
% 4.93/1.87  tff(c_1567, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1503])).
% 4.93/1.87  tff(c_347, plain, (![C_135, A_136, B_137]: (~v1_xboole_0(C_135) | ~v1_funct_2(C_135, A_136, B_137) | ~v1_funct_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | v1_xboole_0(B_137) | v1_xboole_0(A_136))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.93/1.87  tff(c_356, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_347])).
% 4.93/1.87  tff(c_367, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_356])).
% 4.93/1.87  tff(c_368, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_84, c_367])).
% 4.93/1.87  tff(c_370, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_368])).
% 4.93/1.87  tff(c_26, plain, (![B_16, A_14]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.93/1.87  tff(c_1223, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1208, c_26])).
% 4.93/1.87  tff(c_1238, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_370, c_1223])).
% 4.93/1.87  tff(c_1572, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_1238])).
% 4.93/1.87  tff(c_1595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_22, c_1572])).
% 4.93/1.87  tff(c_1597, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1503])).
% 4.93/1.87  tff(c_1704, plain, (![A_313]: (r2_hidden(k1_funct_1('#skF_6', A_313), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_313, '#skF_4'))), inference(resolution, [status(thm)], [c_1208, c_1700])).
% 4.93/1.87  tff(c_1716, plain, (![A_313]: (r2_hidden(k1_funct_1('#skF_6', A_313), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | v1_xboole_0('#skF_4') | ~m1_subset_1(A_313, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1122, c_1704])).
% 4.93/1.87  tff(c_1717, plain, (![A_313]: (r2_hidden(k1_funct_1('#skF_6', A_313), k1_relat_1('#skF_7')) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_313, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1597, c_1716])).
% 4.93/1.87  tff(c_1833, plain, (![A_324]: (r2_hidden(k1_funct_1('#skF_6', A_324), k1_relat_1('#skF_7')) | ~m1_subset_1(A_324, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1759, c_1717])).
% 4.93/1.87  tff(c_48, plain, (![A_35, B_36, C_38]: (k7_partfun1(A_35, B_36, C_38)=k1_funct_1(B_36, C_38) | ~r2_hidden(C_38, k1_relat_1(B_36)) | ~v1_funct_1(B_36) | ~v5_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.93/1.87  tff(c_1837, plain, (![A_35, A_324]: (k7_partfun1(A_35, '#skF_7', k1_funct_1('#skF_6', A_324))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_324)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_35) | ~v1_relat_1('#skF_7') | ~m1_subset_1(A_324, '#skF_4'))), inference(resolution, [status(thm)], [c_1833, c_48])).
% 4.93/1.87  tff(c_1889, plain, (![A_333, A_334]: (k7_partfun1(A_333, '#skF_7', k1_funct_1('#skF_6', A_334))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_334)) | ~v5_relat_1('#skF_7', A_333) | ~m1_subset_1(A_334, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_76, c_1837])).
% 4.93/1.87  tff(c_66, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.93/1.87  tff(c_1895, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1889, c_66])).
% 4.93/1.87  tff(c_1901, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_247, c_1895])).
% 4.93/1.87  tff(c_1923, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1337, c_1901])).
% 4.93/1.87  tff(c_1927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1923])).
% 4.93/1.87  tff(c_1928, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1205])).
% 4.93/1.87  tff(c_1953, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_12])).
% 4.93/1.87  tff(c_1956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1953])).
% 4.93/1.87  tff(c_1957, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1101])).
% 4.93/1.87  tff(c_1977, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_12])).
% 4.93/1.87  tff(c_1980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1977])).
% 4.93/1.87  tff(c_1981, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_368])).
% 4.93/1.87  tff(c_1986, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1981, c_194])).
% 4.93/1.87  tff(c_1995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1986])).
% 4.93/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.87  
% 4.93/1.87  Inference rules
% 4.93/1.87  ----------------------
% 4.93/1.87  #Ref     : 0
% 4.93/1.87  #Sup     : 399
% 4.93/1.87  #Fact    : 0
% 4.93/1.87  #Define  : 0
% 4.93/1.87  #Split   : 26
% 4.93/1.87  #Chain   : 0
% 4.93/1.87  #Close   : 0
% 4.93/1.87  
% 4.93/1.87  Ordering : KBO
% 4.93/1.87  
% 4.93/1.87  Simplification rules
% 4.93/1.87  ----------------------
% 4.93/1.87  #Subsume      : 106
% 4.93/1.87  #Demod        : 416
% 4.93/1.87  #Tautology    : 100
% 4.93/1.87  #SimpNegUnit  : 32
% 4.93/1.87  #BackRed      : 146
% 4.93/1.87  
% 4.93/1.87  #Partial instantiations: 0
% 4.93/1.87  #Strategies tried      : 1
% 4.93/1.87  
% 4.93/1.87  Timing (in seconds)
% 4.93/1.87  ----------------------
% 4.93/1.88  Preprocessing        : 0.37
% 4.93/1.88  Parsing              : 0.19
% 4.93/1.88  CNF conversion       : 0.03
% 4.93/1.88  Main loop            : 0.73
% 4.93/1.88  Inferencing          : 0.23
% 4.93/1.88  Reduction            : 0.23
% 4.93/1.88  Demodulation         : 0.16
% 4.93/1.88  BG Simplification    : 0.03
% 4.93/1.88  Subsumption          : 0.19
% 4.93/1.88  Abstraction          : 0.03
% 4.93/1.88  MUC search           : 0.00
% 4.93/1.88  Cooper               : 0.00
% 4.93/1.88  Total                : 1.15
% 4.93/1.88  Index Insertion      : 0.00
% 4.93/1.88  Index Deletion       : 0.00
% 4.93/1.88  Index Matching       : 0.00
% 4.93/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
