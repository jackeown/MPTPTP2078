%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:48 EST 2020

% Result     : Theorem 26.09s
% Output     : CNFRefutation 26.09s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 249 expanded)
%              Number of leaves         :   43 ( 107 expanded)
%              Depth                    :   12
%              Number of atoms          :  208 ( 857 expanded)
%              Number of equality atoms :   51 ( 199 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_197,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_172,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_76,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_659,plain,(
    ! [A_161,B_162,C_163] :
      ( k1_relset_1(A_161,B_162,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_685,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_659])).

tff(c_553,plain,(
    ! [A_150,B_151,C_152] :
      ( k2_relset_1(A_150,B_151,C_152) = k2_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_578,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_553])).

tff(c_74,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_616,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_74])).

tff(c_695,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_616])).

tff(c_80,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1591,plain,(
    ! [D_228,B_226,C_230,E_229,F_227,A_231] :
      ( k1_funct_1(k8_funct_2(B_226,C_230,A_231,D_228,E_229),F_227) = k1_funct_1(E_229,k1_funct_1(D_228,F_227))
      | k1_xboole_0 = B_226
      | ~ r1_tarski(k2_relset_1(B_226,C_230,D_228),k1_relset_1(C_230,A_231,E_229))
      | ~ m1_subset_1(F_227,B_226)
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(C_230,A_231)))
      | ~ v1_funct_1(E_229)
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(B_226,C_230)))
      | ~ v1_funct_2(D_228,B_226,C_230)
      | ~ v1_funct_1(D_228)
      | v1_xboole_0(C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1597,plain,(
    ! [B_226,D_228,F_227] :
      ( k1_funct_1(k8_funct_2(B_226,'#skF_5','#skF_3',D_228,'#skF_7'),F_227) = k1_funct_1('#skF_7',k1_funct_1(D_228,F_227))
      | k1_xboole_0 = B_226
      | ~ r1_tarski(k2_relset_1(B_226,'#skF_5',D_228),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_227,B_226)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(B_226,'#skF_5')))
      | ~ v1_funct_2(D_228,B_226,'#skF_5')
      | ~ v1_funct_1(D_228)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_1591])).

tff(c_1611,plain,(
    ! [B_226,D_228,F_227] :
      ( k1_funct_1(k8_funct_2(B_226,'#skF_5','#skF_3',D_228,'#skF_7'),F_227) = k1_funct_1('#skF_7',k1_funct_1(D_228,F_227))
      | k1_xboole_0 = B_226
      | ~ r1_tarski(k2_relset_1(B_226,'#skF_5',D_228),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_227,B_226)
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(B_226,'#skF_5')))
      | ~ v1_funct_2(D_228,B_226,'#skF_5')
      | ~ v1_funct_1(D_228)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1597])).

tff(c_1853,plain,(
    ! [B_257,D_258,F_259] :
      ( k1_funct_1(k8_funct_2(B_257,'#skF_5','#skF_3',D_258,'#skF_7'),F_259) = k1_funct_1('#skF_7',k1_funct_1(D_258,F_259))
      | k1_xboole_0 = B_257
      | ~ r1_tarski(k2_relset_1(B_257,'#skF_5',D_258),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_259,B_257)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(B_257,'#skF_5')))
      | ~ v1_funct_2(D_258,B_257,'#skF_5')
      | ~ v1_funct_1(D_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1611])).

tff(c_1861,plain,(
    ! [F_259] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_259) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_259))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_259,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_1853])).

tff(c_1870,plain,(
    ! [F_259] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_259) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_259))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_259,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_695,c_1861])).

tff(c_1871,plain,(
    ! [F_259] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_259) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_259))
      | ~ m1_subset_1(F_259,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1870])).

tff(c_103,plain,(
    ! [B_79,A_80] :
      ( v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,A_80)
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_115,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_103])).

tff(c_116,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_290,plain,(
    ! [C_113,B_114,A_115] :
      ( v5_relat_1(C_113,B_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_313,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_290])).

tff(c_215,plain,(
    ! [C_101,A_102,B_103] :
      ( v1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_232,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_215])).

tff(c_684,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_659])).

tff(c_1149,plain,(
    ! [B_198,A_199,C_200] :
      ( k1_xboole_0 = B_198
      | k1_relset_1(A_199,B_198,C_200) = A_199
      | ~ v1_funct_2(C_200,A_199,B_198)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1170,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1149])).

tff(c_1181,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_684,c_1170])).

tff(c_1184,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1181])).

tff(c_233,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_215])).

tff(c_951,plain,(
    ! [B_179,A_180] :
      ( r2_hidden(k1_funct_1(B_179,A_180),k2_relat_1(B_179))
      | ~ r2_hidden(A_180,k1_relat_1(B_179))
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5453,plain,(
    ! [B_431,A_432,B_433] :
      ( r2_hidden(k1_funct_1(B_431,A_432),B_433)
      | ~ r1_tarski(k2_relat_1(B_431),B_433)
      | ~ r2_hidden(A_432,k1_relat_1(B_431))
      | ~ v1_funct_1(B_431)
      | ~ v1_relat_1(B_431) ) ),
    inference(resolution,[status(thm)],[c_951,c_6])).

tff(c_66,plain,(
    ! [A_42,B_43,C_45] :
      ( k7_partfun1(A_42,B_43,C_45) = k1_funct_1(B_43,C_45)
      | ~ r2_hidden(C_45,k1_relat_1(B_43))
      | ~ v1_funct_1(B_43)
      | ~ v5_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_15820,plain,(
    ! [A_758,B_759,B_760,A_761] :
      ( k7_partfun1(A_758,B_759,k1_funct_1(B_760,A_761)) = k1_funct_1(B_759,k1_funct_1(B_760,A_761))
      | ~ v1_funct_1(B_759)
      | ~ v5_relat_1(B_759,A_758)
      | ~ v1_relat_1(B_759)
      | ~ r1_tarski(k2_relat_1(B_760),k1_relat_1(B_759))
      | ~ r2_hidden(A_761,k1_relat_1(B_760))
      | ~ v1_funct_1(B_760)
      | ~ v1_relat_1(B_760) ) ),
    inference(resolution,[status(thm)],[c_5453,c_66])).

tff(c_15848,plain,(
    ! [A_758,A_761] :
      ( k7_partfun1(A_758,'#skF_7',k1_funct_1('#skF_6',A_761)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_761))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_758)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_761,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_695,c_15820])).

tff(c_36165,plain,(
    ! [A_1110,A_1111] :
      ( k7_partfun1(A_1110,'#skF_7',k1_funct_1('#skF_6',A_1111)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_1111))
      | ~ v5_relat_1('#skF_7',A_1110)
      | ~ r2_hidden(A_1111,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_86,c_1184,c_233,c_80,c_15848])).

tff(c_70,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_36171,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36165,c_70])).

tff(c_36177,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_36171])).

tff(c_36200,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36177])).

tff(c_36203,plain,
    ( ~ m1_subset_1('#skF_8','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_36200])).

tff(c_36206,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_36203])).

tff(c_36208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_36206])).

tff(c_36209,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_36177])).

tff(c_54328,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_36209])).

tff(c_54332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54328])).

tff(c_54333,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1181])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54397,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54333,c_12])).

tff(c_54400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_54397])).

tff(c_54402,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54409,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54402,c_14])).

tff(c_54413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_54409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:09 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.09/15.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.09/15.63  
% 26.09/15.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.09/15.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 26.09/15.64  
% 26.09/15.64  %Foreground sorts:
% 26.09/15.64  
% 26.09/15.64  
% 26.09/15.64  %Background operators:
% 26.09/15.64  
% 26.09/15.64  
% 26.09/15.64  %Foreground operators:
% 26.09/15.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 26.09/15.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 26.09/15.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.09/15.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.09/15.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 26.09/15.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.09/15.64  tff('#skF_7', type, '#skF_7': $i).
% 26.09/15.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.09/15.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 26.09/15.64  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 26.09/15.64  tff('#skF_5', type, '#skF_5': $i).
% 26.09/15.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 26.09/15.64  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 26.09/15.64  tff('#skF_6', type, '#skF_6': $i).
% 26.09/15.64  tff('#skF_3', type, '#skF_3': $i).
% 26.09/15.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 26.09/15.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 26.09/15.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.09/15.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 26.09/15.64  tff('#skF_8', type, '#skF_8': $i).
% 26.09/15.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.09/15.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 26.09/15.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 26.09/15.64  tff('#skF_4', type, '#skF_4': $i).
% 26.09/15.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.09/15.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 26.09/15.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 26.09/15.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 26.09/15.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 26.09/15.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.09/15.64  
% 26.09/15.65  tff(f_197, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 26.09/15.65  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 26.09/15.65  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 26.09/15.65  tff(f_172, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 26.09/15.65  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 26.09/15.65  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 26.09/15.65  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 26.09/15.65  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 26.09/15.65  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 26.09/15.65  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 26.09/15.65  tff(f_148, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 26.09/15.65  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 26.09/15.65  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 26.09/15.65  tff(c_72, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_88, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_76, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_659, plain, (![A_161, B_162, C_163]: (k1_relset_1(A_161, B_162, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.09/15.65  tff(c_685, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_659])).
% 26.09/15.65  tff(c_553, plain, (![A_150, B_151, C_152]: (k2_relset_1(A_150, B_151, C_152)=k2_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 26.09/15.65  tff(c_578, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_553])).
% 26.09/15.65  tff(c_74, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_616, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_74])).
% 26.09/15.65  tff(c_695, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_685, c_616])).
% 26.09/15.65  tff(c_80, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_1591, plain, (![D_228, B_226, C_230, E_229, F_227, A_231]: (k1_funct_1(k8_funct_2(B_226, C_230, A_231, D_228, E_229), F_227)=k1_funct_1(E_229, k1_funct_1(D_228, F_227)) | k1_xboole_0=B_226 | ~r1_tarski(k2_relset_1(B_226, C_230, D_228), k1_relset_1(C_230, A_231, E_229)) | ~m1_subset_1(F_227, B_226) | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(C_230, A_231))) | ~v1_funct_1(E_229) | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(B_226, C_230))) | ~v1_funct_2(D_228, B_226, C_230) | ~v1_funct_1(D_228) | v1_xboole_0(C_230))), inference(cnfTransformation, [status(thm)], [f_172])).
% 26.09/15.65  tff(c_1597, plain, (![B_226, D_228, F_227]: (k1_funct_1(k8_funct_2(B_226, '#skF_5', '#skF_3', D_228, '#skF_7'), F_227)=k1_funct_1('#skF_7', k1_funct_1(D_228, F_227)) | k1_xboole_0=B_226 | ~r1_tarski(k2_relset_1(B_226, '#skF_5', D_228), k1_relat_1('#skF_7')) | ~m1_subset_1(F_227, B_226) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(B_226, '#skF_5'))) | ~v1_funct_2(D_228, B_226, '#skF_5') | ~v1_funct_1(D_228) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_685, c_1591])).
% 26.09/15.65  tff(c_1611, plain, (![B_226, D_228, F_227]: (k1_funct_1(k8_funct_2(B_226, '#skF_5', '#skF_3', D_228, '#skF_7'), F_227)=k1_funct_1('#skF_7', k1_funct_1(D_228, F_227)) | k1_xboole_0=B_226 | ~r1_tarski(k2_relset_1(B_226, '#skF_5', D_228), k1_relat_1('#skF_7')) | ~m1_subset_1(F_227, B_226) | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(B_226, '#skF_5'))) | ~v1_funct_2(D_228, B_226, '#skF_5') | ~v1_funct_1(D_228) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1597])).
% 26.09/15.65  tff(c_1853, plain, (![B_257, D_258, F_259]: (k1_funct_1(k8_funct_2(B_257, '#skF_5', '#skF_3', D_258, '#skF_7'), F_259)=k1_funct_1('#skF_7', k1_funct_1(D_258, F_259)) | k1_xboole_0=B_257 | ~r1_tarski(k2_relset_1(B_257, '#skF_5', D_258), k1_relat_1('#skF_7')) | ~m1_subset_1(F_259, B_257) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(B_257, '#skF_5'))) | ~v1_funct_2(D_258, B_257, '#skF_5') | ~v1_funct_1(D_258))), inference(negUnitSimplification, [status(thm)], [c_88, c_1611])).
% 26.09/15.65  tff(c_1861, plain, (![F_259]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_259)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_259)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_259, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_578, c_1853])).
% 26.09/15.65  tff(c_1870, plain, (![F_259]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_259)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_259)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_259, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_695, c_1861])).
% 26.09/15.65  tff(c_1871, plain, (![F_259]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_259)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_259)) | ~m1_subset_1(F_259, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1870])).
% 26.09/15.65  tff(c_103, plain, (![B_79, A_80]: (v1_xboole_0(B_79) | ~m1_subset_1(B_79, A_80) | ~v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_62])).
% 26.09/15.65  tff(c_115, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_76, c_103])).
% 26.09/15.65  tff(c_116, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_115])).
% 26.09/15.65  tff(c_24, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 26.09/15.65  tff(c_290, plain, (![C_113, B_114, A_115]: (v5_relat_1(C_113, B_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 26.09/15.65  tff(c_313, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_290])).
% 26.09/15.65  tff(c_215, plain, (![C_101, A_102, B_103]: (v1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 26.09/15.65  tff(c_232, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_215])).
% 26.09/15.65  tff(c_684, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_659])).
% 26.09/15.65  tff(c_1149, plain, (![B_198, A_199, C_200]: (k1_xboole_0=B_198 | k1_relset_1(A_199, B_198, C_200)=A_199 | ~v1_funct_2(C_200, A_199, B_198) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 26.09/15.65  tff(c_1170, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_1149])).
% 26.09/15.65  tff(c_1181, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_684, c_1170])).
% 26.09/15.65  tff(c_1184, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1181])).
% 26.09/15.65  tff(c_233, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_215])).
% 26.09/15.65  tff(c_951, plain, (![B_179, A_180]: (r2_hidden(k1_funct_1(B_179, A_180), k2_relat_1(B_179)) | ~r2_hidden(A_180, k1_relat_1(B_179)) | ~v1_funct_1(B_179) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_74])).
% 26.09/15.65  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 26.09/15.65  tff(c_5453, plain, (![B_431, A_432, B_433]: (r2_hidden(k1_funct_1(B_431, A_432), B_433) | ~r1_tarski(k2_relat_1(B_431), B_433) | ~r2_hidden(A_432, k1_relat_1(B_431)) | ~v1_funct_1(B_431) | ~v1_relat_1(B_431))), inference(resolution, [status(thm)], [c_951, c_6])).
% 26.09/15.65  tff(c_66, plain, (![A_42, B_43, C_45]: (k7_partfun1(A_42, B_43, C_45)=k1_funct_1(B_43, C_45) | ~r2_hidden(C_45, k1_relat_1(B_43)) | ~v1_funct_1(B_43) | ~v5_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_148])).
% 26.09/15.65  tff(c_15820, plain, (![A_758, B_759, B_760, A_761]: (k7_partfun1(A_758, B_759, k1_funct_1(B_760, A_761))=k1_funct_1(B_759, k1_funct_1(B_760, A_761)) | ~v1_funct_1(B_759) | ~v5_relat_1(B_759, A_758) | ~v1_relat_1(B_759) | ~r1_tarski(k2_relat_1(B_760), k1_relat_1(B_759)) | ~r2_hidden(A_761, k1_relat_1(B_760)) | ~v1_funct_1(B_760) | ~v1_relat_1(B_760))), inference(resolution, [status(thm)], [c_5453, c_66])).
% 26.09/15.65  tff(c_15848, plain, (![A_758, A_761]: (k7_partfun1(A_758, '#skF_7', k1_funct_1('#skF_6', A_761))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_761)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_758) | ~v1_relat_1('#skF_7') | ~r2_hidden(A_761, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_695, c_15820])).
% 26.09/15.65  tff(c_36165, plain, (![A_1110, A_1111]: (k7_partfun1(A_1110, '#skF_7', k1_funct_1('#skF_6', A_1111))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_1111)) | ~v5_relat_1('#skF_7', A_1110) | ~r2_hidden(A_1111, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_86, c_1184, c_233, c_80, c_15848])).
% 26.09/15.65  tff(c_70, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_197])).
% 26.09/15.65  tff(c_36171, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36165, c_70])).
% 26.09/15.65  tff(c_36177, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_36171])).
% 26.09/15.65  tff(c_36200, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_36177])).
% 26.09/15.65  tff(c_36203, plain, (~m1_subset_1('#skF_8', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_36200])).
% 26.09/15.65  tff(c_36206, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_36203])).
% 26.09/15.65  tff(c_36208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_36206])).
% 26.09/15.65  tff(c_36209, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_36177])).
% 26.09/15.65  tff(c_54328, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1871, c_36209])).
% 26.09/15.65  tff(c_54332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_54328])).
% 26.09/15.65  tff(c_54333, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1181])).
% 26.09/15.65  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 26.09/15.65  tff(c_54397, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54333, c_12])).
% 26.09/15.65  tff(c_54400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_54397])).
% 26.09/15.65  tff(c_54402, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_115])).
% 26.09/15.65  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.09/15.65  tff(c_54409, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_54402, c_14])).
% 26.09/15.65  tff(c_54413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_54409])).
% 26.09/15.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.09/15.65  
% 26.09/15.65  Inference rules
% 26.09/15.65  ----------------------
% 26.09/15.65  #Ref     : 0
% 26.09/15.65  #Sup     : 13145
% 26.09/15.65  #Fact    : 0
% 26.09/15.65  #Define  : 0
% 26.09/15.65  #Split   : 95
% 26.09/15.65  #Chain   : 0
% 26.09/15.65  #Close   : 0
% 26.09/15.65  
% 26.09/15.65  Ordering : KBO
% 26.09/15.65  
% 26.09/15.65  Simplification rules
% 26.09/15.65  ----------------------
% 26.09/15.65  #Subsume      : 5196
% 26.09/15.65  #Demod        : 9003
% 26.09/15.65  #Tautology    : 3088
% 26.09/15.65  #SimpNegUnit  : 980
% 26.09/15.65  #BackRed      : 472
% 26.09/15.65  
% 26.09/15.65  #Partial instantiations: 0
% 26.09/15.65  #Strategies tried      : 1
% 26.09/15.65  
% 26.09/15.65  Timing (in seconds)
% 26.09/15.65  ----------------------
% 26.09/15.66  Preprocessing        : 0.39
% 26.09/15.66  Parsing              : 0.20
% 26.09/15.66  CNF conversion       : 0.03
% 26.09/15.66  Main loop            : 14.49
% 26.09/15.66  Inferencing          : 2.28
% 26.09/15.66  Reduction            : 4.16
% 26.09/15.66  Demodulation         : 2.91
% 26.09/15.66  BG Simplification    : 0.21
% 26.09/15.66  Subsumption          : 7.00
% 26.09/15.66  Abstraction          : 0.39
% 26.09/15.66  MUC search           : 0.00
% 26.09/15.66  Cooper               : 0.00
% 26.09/15.66  Total                : 14.91
% 26.09/15.66  Index Insertion      : 0.00
% 26.09/15.66  Index Deletion       : 0.00
% 26.09/15.66  Index Matching       : 0.00
% 26.09/15.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
