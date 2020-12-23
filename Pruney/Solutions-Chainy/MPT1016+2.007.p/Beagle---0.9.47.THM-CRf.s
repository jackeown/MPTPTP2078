%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:41 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 454 expanded)
%              Number of leaves         :   33 ( 165 expanded)
%              Depth                    :   15
%              Number of atoms          :  295 (1619 expanded)
%              Number of equality atoms :   76 ( 411 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_72,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_72])).

tff(c_132,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_141,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_188,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_1'(A_76),k1_relat_1(A_76))
      | v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_773,plain,(
    ! [A_133,A_134] :
      ( r2_hidden('#skF_1'(A_133),A_134)
      | ~ m1_subset_1(k1_relat_1(A_133),k1_zfmisc_1(A_134))
      | v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(resolution,[status(thm)],[c_188,c_4])).

tff(c_1040,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166),B_167)
      | v2_funct_1(A_166)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166)
      | ~ r1_tarski(k1_relat_1(A_166),B_167) ) ),
    inference(resolution,[status(thm)],[c_8,c_773])).

tff(c_164,plain,(
    ! [A_68] :
      ( '#skF_2'(A_68) != '#skF_1'(A_68)
      | v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_167,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_164,c_60])).

tff(c_170,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_38,c_167])).

tff(c_180,plain,(
    ! [A_75] :
      ( r2_hidden('#skF_2'(A_75),k1_relat_1(A_75))
      | v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_565,plain,(
    ! [A_112,A_113] :
      ( r2_hidden('#skF_2'(A_112),A_113)
      | ~ m1_subset_1(k1_relat_1(A_112),k1_zfmisc_1(A_113))
      | v2_funct_1(A_112)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_573,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_2'(A_115),B_116)
      | v2_funct_1(A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115)
      | ~ r1_tarski(k1_relat_1(A_115),B_116) ) ),
    inference(resolution,[status(thm)],[c_8,c_565])).

tff(c_233,plain,(
    ! [A_85] :
      ( k1_funct_1(A_85,'#skF_2'(A_85)) = k1_funct_1(A_85,'#skF_1'(A_85))
      | v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    ! [D_34,C_33] :
      ( v2_funct_1('#skF_4')
      | D_34 = C_33
      | k1_funct_1('#skF_4',D_34) != k1_funct_1('#skF_4',C_33)
      | ~ r2_hidden(D_34,'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_103,plain,(
    ! [D_34,C_33] :
      ( D_34 = C_33
      | k1_funct_1('#skF_4',D_34) != k1_funct_1('#skF_4',C_33)
      | ~ r2_hidden(D_34,'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58])).

tff(c_242,plain,(
    ! [D_34] :
      ( D_34 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_34) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_34,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_103])).

tff(c_251,plain,(
    ! [D_34] :
      ( D_34 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_34) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_34,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_38,c_242])).

tff(c_252,plain,(
    ! [D_34] :
      ( D_34 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_34) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_34,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_251])).

tff(c_366,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_578,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_573,c_366])).

tff(c_587,plain,
    ( v2_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_38,c_578])).

tff(c_588,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_587])).

tff(c_593,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_588])).

tff(c_597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_141,c_593])).

tff(c_599,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_239,plain,(
    ! [C_33] :
      ( C_33 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_33) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_103])).

tff(c_248,plain,(
    ! [C_33] :
      ( C_33 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_33) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_38,c_239])).

tff(c_249,plain,(
    ! [C_33] :
      ( C_33 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_33) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_248])).

tff(c_660,plain,(
    ! [C_33] :
      ( C_33 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_33) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(C_33,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_249])).

tff(c_663,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_660])).

tff(c_664,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_663])).

tff(c_1045,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1040,c_664])).

tff(c_1054,plain,
    ( v2_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_38,c_1045])).

tff(c_1055,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1054])).

tff(c_1060,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1055])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_141,c_1060])).

tff(c_1066,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1068,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_44])).

tff(c_1758,plain,(
    ! [D_265,C_266,B_267,A_268] :
      ( k1_funct_1(k2_funct_1(D_265),k1_funct_1(D_265,C_266)) = C_266
      | k1_xboole_0 = B_267
      | ~ r2_hidden(C_266,A_268)
      | ~ v2_funct_1(D_265)
      | ~ m1_subset_1(D_265,k1_zfmisc_1(k2_zfmisc_1(A_268,B_267)))
      | ~ v1_funct_2(D_265,A_268,B_267)
      | ~ v1_funct_1(D_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1815,plain,(
    ! [D_271,B_272] :
      ( k1_funct_1(k2_funct_1(D_271),k1_funct_1(D_271,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_272
      | ~ v2_funct_1(D_271)
      | ~ m1_subset_1(D_271,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_272)))
      | ~ v1_funct_2(D_271,'#skF_3',B_272)
      | ~ v1_funct_1(D_271) ) ),
    inference(resolution,[status(thm)],[c_1068,c_1758])).

tff(c_1820,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1815])).

tff(c_1824,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1066,c_1820])).

tff(c_1883,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1824])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1906,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_2])).

tff(c_1065,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1183,plain,(
    ! [C_199,A_200,B_201] :
      ( r2_hidden(C_199,A_200)
      | ~ r2_hidden(C_199,B_201)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1214,plain,(
    ! [A_205] :
      ( r2_hidden('#skF_6',A_205)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_205)) ) ),
    inference(resolution,[status(thm)],[c_1068,c_1183])).

tff(c_1219,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_6',B_7)
      | ~ r1_tarski('#skF_3',B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_1214])).

tff(c_42,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1091,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_42])).

tff(c_46,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1070,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_46])).

tff(c_1467,plain,(
    ! [D_243,C_244,B_245,A_246] :
      ( k1_funct_1(k2_funct_1(D_243),k1_funct_1(D_243,C_244)) = C_244
      | k1_xboole_0 = B_245
      | ~ r2_hidden(C_244,A_246)
      | ~ v2_funct_1(D_243)
      | ~ m1_subset_1(D_243,k1_zfmisc_1(k2_zfmisc_1(A_246,B_245)))
      | ~ v1_funct_2(D_243,A_246,B_245)
      | ~ v1_funct_1(D_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1521,plain,(
    ! [D_249,B_250] :
      ( k1_funct_1(k2_funct_1(D_249),k1_funct_1(D_249,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_250
      | ~ v2_funct_1(D_249)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_250)))
      | ~ v1_funct_2(D_249,'#skF_3',B_250)
      | ~ v1_funct_1(D_249) ) ),
    inference(resolution,[status(thm)],[c_1070,c_1467])).

tff(c_1526,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1521])).

tff(c_1530,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1066,c_1091,c_1526])).

tff(c_1573,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1530])).

tff(c_1599,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1573,c_2])).

tff(c_1190,plain,(
    ! [A_202] :
      ( r2_hidden('#skF_5',A_202)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_202)) ) ),
    inference(resolution,[status(thm)],[c_1070,c_1183])).

tff(c_1195,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_5',B_7)
      | ~ r1_tarski('#skF_3',B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_1190])).

tff(c_1096,plain,(
    ! [C_174,A_175,B_176] :
      ( v1_relat_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1096])).

tff(c_1413,plain,(
    ! [C_238,B_239,A_240] :
      ( C_238 = B_239
      | k1_funct_1(A_240,C_238) != k1_funct_1(A_240,B_239)
      | ~ r2_hidden(C_238,k1_relat_1(A_240))
      | ~ r2_hidden(B_239,k1_relat_1(A_240))
      | ~ v2_funct_1(A_240)
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1419,plain,(
    ! [B_239] :
      ( B_239 = '#skF_5'
      | k1_funct_1('#skF_4',B_239) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_239,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_1413])).

tff(c_1423,plain,(
    ! [B_239] :
      ( B_239 = '#skF_5'
      | k1_funct_1('#skF_4',B_239) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_239,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1105,c_38,c_1066,c_1419])).

tff(c_1427,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1423])).

tff(c_1431,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1195,c_1427])).

tff(c_1644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1599,c_1431])).

tff(c_1646,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1530])).

tff(c_1645,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1530])).

tff(c_1696,plain,(
    ! [D_261,B_262] :
      ( k1_funct_1(k2_funct_1(D_261),k1_funct_1(D_261,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_262
      | ~ v2_funct_1(D_261)
      | ~ m1_subset_1(D_261,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_262)))
      | ~ v1_funct_2(D_261,'#skF_3',B_262)
      | ~ v1_funct_1(D_261) ) ),
    inference(resolution,[status(thm)],[c_1068,c_1467])).

tff(c_1701,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1696])).

tff(c_1705,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1066,c_1645,c_1701])).

tff(c_1707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1646,c_1065,c_1705])).

tff(c_1846,plain,(
    ! [B_276] :
      ( B_276 = '#skF_5'
      | k1_funct_1('#skF_4',B_276) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_276,k1_relat_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1423])).

tff(c_1861,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1219,c_1846])).

tff(c_1878,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_1861])).

tff(c_1980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1906,c_1878])).

tff(c_1982,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1824])).

tff(c_1981,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1824])).

tff(c_1991,plain,(
    ! [D_281,B_282] :
      ( k1_funct_1(k2_funct_1(D_281),k1_funct_1(D_281,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_282
      | ~ v2_funct_1(D_281)
      | ~ m1_subset_1(D_281,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_282)))
      | ~ v1_funct_2(D_281,'#skF_3',B_282)
      | ~ v1_funct_1(D_281) ) ),
    inference(resolution,[status(thm)],[c_1070,c_1758])).

tff(c_1996,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1991])).

tff(c_2000,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1066,c_1981,c_1091,c_1996])).

tff(c_2002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1982,c_1065,c_2000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.67  
% 4.03/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.03/1.67  
% 4.03/1.67  %Foreground sorts:
% 4.03/1.67  
% 4.03/1.67  
% 4.03/1.67  %Background operators:
% 4.03/1.67  
% 4.03/1.67  
% 4.03/1.67  %Foreground operators:
% 4.03/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.03/1.67  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.03/1.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.03/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.03/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.03/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.03/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.03/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.03/1.67  tff('#skF_5', type, '#skF_5': $i).
% 4.03/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.03/1.67  tff('#skF_6', type, '#skF_6': $i).
% 4.03/1.67  tff('#skF_3', type, '#skF_3': $i).
% 4.03/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.03/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.03/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.03/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.03/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.03/1.67  tff('#skF_4', type, '#skF_4': $i).
% 4.03/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.03/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.03/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.03/1.67  
% 4.03/1.69  tff(f_106, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 4.03/1.69  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.03/1.69  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.03/1.69  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.03/1.69  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.03/1.69  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 4.03/1.69  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.03/1.69  tff(f_88, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 4.03/1.69  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.03/1.69  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_72, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.69  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_72])).
% 4.03/1.69  tff(c_132, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.03/1.69  tff(c_141, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_132])).
% 4.03/1.69  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.03/1.69  tff(c_40, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_60, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 4.03/1.69  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.03/1.69  tff(c_188, plain, (![A_76]: (r2_hidden('#skF_1'(A_76), k1_relat_1(A_76)) | v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.03/1.69  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.03/1.69  tff(c_773, plain, (![A_133, A_134]: (r2_hidden('#skF_1'(A_133), A_134) | ~m1_subset_1(k1_relat_1(A_133), k1_zfmisc_1(A_134)) | v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(resolution, [status(thm)], [c_188, c_4])).
% 4.03/1.69  tff(c_1040, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166), B_167) | v2_funct_1(A_166) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166) | ~r1_tarski(k1_relat_1(A_166), B_167))), inference(resolution, [status(thm)], [c_8, c_773])).
% 4.03/1.69  tff(c_164, plain, (![A_68]: ('#skF_2'(A_68)!='#skF_1'(A_68) | v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.03/1.69  tff(c_167, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_164, c_60])).
% 4.03/1.69  tff(c_170, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_38, c_167])).
% 4.03/1.69  tff(c_180, plain, (![A_75]: (r2_hidden('#skF_2'(A_75), k1_relat_1(A_75)) | v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.03/1.69  tff(c_565, plain, (![A_112, A_113]: (r2_hidden('#skF_2'(A_112), A_113) | ~m1_subset_1(k1_relat_1(A_112), k1_zfmisc_1(A_113)) | v2_funct_1(A_112) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_180, c_4])).
% 4.03/1.69  tff(c_573, plain, (![A_115, B_116]: (r2_hidden('#skF_2'(A_115), B_116) | v2_funct_1(A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115) | ~r1_tarski(k1_relat_1(A_115), B_116))), inference(resolution, [status(thm)], [c_8, c_565])).
% 4.03/1.69  tff(c_233, plain, (![A_85]: (k1_funct_1(A_85, '#skF_2'(A_85))=k1_funct_1(A_85, '#skF_1'(A_85)) | v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.03/1.69  tff(c_58, plain, (![D_34, C_33]: (v2_funct_1('#skF_4') | D_34=C_33 | k1_funct_1('#skF_4', D_34)!=k1_funct_1('#skF_4', C_33) | ~r2_hidden(D_34, '#skF_3') | ~r2_hidden(C_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_103, plain, (![D_34, C_33]: (D_34=C_33 | k1_funct_1('#skF_4', D_34)!=k1_funct_1('#skF_4', C_33) | ~r2_hidden(D_34, '#skF_3') | ~r2_hidden(C_33, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_58])).
% 4.03/1.69  tff(c_242, plain, (![D_34]: (D_34='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_34)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_34, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_233, c_103])).
% 4.03/1.69  tff(c_251, plain, (![D_34]: (D_34='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_34)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_34, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_38, c_242])).
% 4.03/1.69  tff(c_252, plain, (![D_34]: (D_34='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_34)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_34, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_251])).
% 4.03/1.69  tff(c_366, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_252])).
% 4.03/1.69  tff(c_578, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_573, c_366])).
% 4.03/1.69  tff(c_587, plain, (v2_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_38, c_578])).
% 4.03/1.69  tff(c_588, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_587])).
% 4.03/1.69  tff(c_593, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_588])).
% 4.03/1.69  tff(c_597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_141, c_593])).
% 4.03/1.69  tff(c_599, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_252])).
% 4.03/1.69  tff(c_239, plain, (![C_33]: (C_33='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_33)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_33, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_233, c_103])).
% 4.03/1.69  tff(c_248, plain, (![C_33]: (C_33='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_33)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_33, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_38, c_239])).
% 4.03/1.69  tff(c_249, plain, (![C_33]: (C_33='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_33)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_33, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_248])).
% 4.03/1.69  tff(c_660, plain, (![C_33]: (C_33='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_33)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(C_33, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_249])).
% 4.03/1.69  tff(c_663, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_660])).
% 4.03/1.69  tff(c_664, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_170, c_663])).
% 4.03/1.69  tff(c_1045, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1040, c_664])).
% 4.03/1.69  tff(c_1054, plain, (v2_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_38, c_1045])).
% 4.03/1.69  tff(c_1055, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_1054])).
% 4.03/1.69  tff(c_1060, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_1055])).
% 4.03/1.69  tff(c_1064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_141, c_1060])).
% 4.03/1.69  tff(c_1066, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 4.03/1.69  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_1068, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_44])).
% 4.03/1.69  tff(c_1758, plain, (![D_265, C_266, B_267, A_268]: (k1_funct_1(k2_funct_1(D_265), k1_funct_1(D_265, C_266))=C_266 | k1_xboole_0=B_267 | ~r2_hidden(C_266, A_268) | ~v2_funct_1(D_265) | ~m1_subset_1(D_265, k1_zfmisc_1(k2_zfmisc_1(A_268, B_267))) | ~v1_funct_2(D_265, A_268, B_267) | ~v1_funct_1(D_265))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.03/1.69  tff(c_1815, plain, (![D_271, B_272]: (k1_funct_1(k2_funct_1(D_271), k1_funct_1(D_271, '#skF_6'))='#skF_6' | k1_xboole_0=B_272 | ~v2_funct_1(D_271) | ~m1_subset_1(D_271, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_272))) | ~v1_funct_2(D_271, '#skF_3', B_272) | ~v1_funct_1(D_271))), inference(resolution, [status(thm)], [c_1068, c_1758])).
% 4.03/1.69  tff(c_1820, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1815])).
% 4.03/1.69  tff(c_1824, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1066, c_1820])).
% 4.03/1.69  tff(c_1883, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1824])).
% 4.03/1.69  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.03/1.69  tff(c_1906, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_2])).
% 4.03/1.69  tff(c_1065, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 4.03/1.69  tff(c_1183, plain, (![C_199, A_200, B_201]: (r2_hidden(C_199, A_200) | ~r2_hidden(C_199, B_201) | ~m1_subset_1(B_201, k1_zfmisc_1(A_200)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.03/1.69  tff(c_1214, plain, (![A_205]: (r2_hidden('#skF_6', A_205) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_205)))), inference(resolution, [status(thm)], [c_1068, c_1183])).
% 4.03/1.69  tff(c_1219, plain, (![B_7]: (r2_hidden('#skF_6', B_7) | ~r1_tarski('#skF_3', B_7))), inference(resolution, [status(thm)], [c_8, c_1214])).
% 4.03/1.69  tff(c_42, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_1091, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_42])).
% 4.03/1.69  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_1070, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_46])).
% 4.03/1.69  tff(c_1467, plain, (![D_243, C_244, B_245, A_246]: (k1_funct_1(k2_funct_1(D_243), k1_funct_1(D_243, C_244))=C_244 | k1_xboole_0=B_245 | ~r2_hidden(C_244, A_246) | ~v2_funct_1(D_243) | ~m1_subset_1(D_243, k1_zfmisc_1(k2_zfmisc_1(A_246, B_245))) | ~v1_funct_2(D_243, A_246, B_245) | ~v1_funct_1(D_243))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.03/1.69  tff(c_1521, plain, (![D_249, B_250]: (k1_funct_1(k2_funct_1(D_249), k1_funct_1(D_249, '#skF_5'))='#skF_5' | k1_xboole_0=B_250 | ~v2_funct_1(D_249) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_250))) | ~v1_funct_2(D_249, '#skF_3', B_250) | ~v1_funct_1(D_249))), inference(resolution, [status(thm)], [c_1070, c_1467])).
% 4.03/1.69  tff(c_1526, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1521])).
% 4.03/1.69  tff(c_1530, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1066, c_1091, c_1526])).
% 4.03/1.69  tff(c_1573, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1530])).
% 4.03/1.69  tff(c_1599, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1573, c_2])).
% 4.03/1.69  tff(c_1190, plain, (![A_202]: (r2_hidden('#skF_5', A_202) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_202)))), inference(resolution, [status(thm)], [c_1070, c_1183])).
% 4.03/1.69  tff(c_1195, plain, (![B_7]: (r2_hidden('#skF_5', B_7) | ~r1_tarski('#skF_3', B_7))), inference(resolution, [status(thm)], [c_8, c_1190])).
% 4.03/1.69  tff(c_1096, plain, (![C_174, A_175, B_176]: (v1_relat_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.69  tff(c_1105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1096])).
% 4.03/1.69  tff(c_1413, plain, (![C_238, B_239, A_240]: (C_238=B_239 | k1_funct_1(A_240, C_238)!=k1_funct_1(A_240, B_239) | ~r2_hidden(C_238, k1_relat_1(A_240)) | ~r2_hidden(B_239, k1_relat_1(A_240)) | ~v2_funct_1(A_240) | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.03/1.69  tff(c_1419, plain, (![B_239]: (B_239='#skF_5' | k1_funct_1('#skF_4', B_239)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_239, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_1413])).
% 4.03/1.69  tff(c_1423, plain, (![B_239]: (B_239='#skF_5' | k1_funct_1('#skF_4', B_239)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_239, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1105, c_38, c_1066, c_1419])).
% 4.03/1.69  tff(c_1427, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1423])).
% 4.03/1.69  tff(c_1431, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1195, c_1427])).
% 4.03/1.69  tff(c_1644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1599, c_1431])).
% 4.03/1.69  tff(c_1646, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1530])).
% 4.03/1.69  tff(c_1645, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1530])).
% 4.03/1.69  tff(c_1696, plain, (![D_261, B_262]: (k1_funct_1(k2_funct_1(D_261), k1_funct_1(D_261, '#skF_6'))='#skF_6' | k1_xboole_0=B_262 | ~v2_funct_1(D_261) | ~m1_subset_1(D_261, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_262))) | ~v1_funct_2(D_261, '#skF_3', B_262) | ~v1_funct_1(D_261))), inference(resolution, [status(thm)], [c_1068, c_1467])).
% 4.03/1.69  tff(c_1701, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1696])).
% 4.03/1.69  tff(c_1705, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1066, c_1645, c_1701])).
% 4.03/1.69  tff(c_1707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1646, c_1065, c_1705])).
% 4.03/1.69  tff(c_1846, plain, (![B_276]: (B_276='#skF_5' | k1_funct_1('#skF_4', B_276)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_276, k1_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1423])).
% 4.03/1.69  tff(c_1861, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1219, c_1846])).
% 4.03/1.69  tff(c_1878, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1065, c_1861])).
% 4.03/1.69  tff(c_1980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1906, c_1878])).
% 4.03/1.69  tff(c_1982, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1824])).
% 4.03/1.69  tff(c_1981, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1824])).
% 4.03/1.69  tff(c_1991, plain, (![D_281, B_282]: (k1_funct_1(k2_funct_1(D_281), k1_funct_1(D_281, '#skF_5'))='#skF_5' | k1_xboole_0=B_282 | ~v2_funct_1(D_281) | ~m1_subset_1(D_281, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_282))) | ~v1_funct_2(D_281, '#skF_3', B_282) | ~v1_funct_1(D_281))), inference(resolution, [status(thm)], [c_1070, c_1758])).
% 4.03/1.69  tff(c_1996, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1991])).
% 4.03/1.69  tff(c_2000, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1066, c_1981, c_1091, c_1996])).
% 4.03/1.69  tff(c_2002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1982, c_1065, c_2000])).
% 4.03/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.69  
% 4.03/1.69  Inference rules
% 4.03/1.69  ----------------------
% 4.03/1.69  #Ref     : 5
% 4.03/1.69  #Sup     : 313
% 4.03/1.69  #Fact    : 0
% 4.03/1.69  #Define  : 0
% 4.03/1.69  #Split   : 19
% 4.03/1.69  #Chain   : 0
% 4.03/1.69  #Close   : 0
% 4.03/1.69  
% 4.03/1.69  Ordering : KBO
% 4.03/1.69  
% 4.03/1.69  Simplification rules
% 4.03/1.69  ----------------------
% 4.03/1.69  #Subsume      : 31
% 4.03/1.69  #Demod        : 286
% 4.03/1.69  #Tautology    : 46
% 4.03/1.69  #SimpNegUnit  : 10
% 4.03/1.69  #BackRed      : 77
% 4.03/1.69  
% 4.03/1.69  #Partial instantiations: 0
% 4.03/1.69  #Strategies tried      : 1
% 4.03/1.69  
% 4.03/1.69  Timing (in seconds)
% 4.03/1.69  ----------------------
% 4.03/1.69  Preprocessing        : 0.31
% 4.03/1.69  Parsing              : 0.16
% 4.03/1.69  CNF conversion       : 0.02
% 4.03/1.69  Main loop            : 0.61
% 4.03/1.69  Inferencing          : 0.22
% 4.03/1.69  Reduction            : 0.21
% 4.03/1.69  Demodulation         : 0.15
% 4.03/1.69  BG Simplification    : 0.03
% 4.03/1.69  Subsumption          : 0.11
% 4.03/1.69  Abstraction          : 0.03
% 4.03/1.69  MUC search           : 0.00
% 4.03/1.69  Cooper               : 0.00
% 4.03/1.69  Total                : 0.97
% 4.03/1.69  Index Insertion      : 0.00
% 4.03/1.69  Index Deletion       : 0.00
% 4.03/1.69  Index Matching       : 0.00
% 4.03/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
