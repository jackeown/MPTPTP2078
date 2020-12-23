%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:00 EST 2020

% Result     : Theorem 5.21s
% Output     : CNFRefutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 223 expanded)
%              Number of leaves         :   29 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  183 ( 668 expanded)
%              Number of equality atoms :   32 ( 100 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
            <=> ! [D] :
                  ( r2_hidden(D,k1_relset_1(A,A,B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_34,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_55,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_45,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_53,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_83,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_83])).

tff(c_139,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1(k1_relset_1(A_65,B_66,C_67),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_156,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_139])).

tff(c_163,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_156])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [C_50,A_51,B_52] :
      ( r2_hidden(C_50,A_51)
      | ~ r2_hidden(C_50,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_60,B_61,A_62] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_62)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(A_62))
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_60,A_62] :
      ( ~ m1_subset_1(A_60,k1_zfmisc_1(A_62))
      | r1_tarski(A_60,A_62) ) ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_171,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_163,c_129])).

tff(c_26,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_91,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_83])).

tff(c_221,plain,(
    ! [A_78,B_79] :
      ( k1_relset_1(A_78,A_78,B_79) = A_78
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_zfmisc_1(A_78,A_78)))
      | ~ v1_funct_2(B_79,A_78,A_78)
      | ~ v1_funct_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_231,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_221])).

tff(c_238,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_91,c_231])).

tff(c_280,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_2'(A_83,B_84),k1_relat_1(A_83))
      | r1_partfun1(A_83,B_84)
      | ~ r1_tarski(k1_relat_1(A_83),k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    ! [D_38] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',D_38) = k1_funct_1('#skF_4',D_38)
      | ~ r2_hidden(D_38,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_96,plain,(
    ! [D_38] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',D_38) = k1_funct_1('#skF_4',D_38)
      | ~ r2_hidden(D_38,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_44])).

tff(c_97,plain,(
    ! [D_38] :
      ( k1_funct_1('#skF_5',D_38) = k1_funct_1('#skF_4',D_38)
      | ~ r2_hidden(D_38,k1_relat_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_96])).

tff(c_284,plain,(
    ! [B_84] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_4',B_84)) = k1_funct_1('#skF_4','#skF_2'('#skF_4',B_84))
      | r1_partfun1('#skF_4',B_84)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_280,c_97])).

tff(c_1499,plain,(
    ! [B_277] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_4',B_277)) = k1_funct_1('#skF_4','#skF_2'('#skF_4',B_277))
      | r1_partfun1('#skF_4',B_277)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_277))
      | ~ v1_funct_1(B_277)
      | ~ v1_relat_1(B_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_32,c_284])).

tff(c_1502,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_2'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_1499])).

tff(c_1508,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_2'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_28,c_171,c_1502])).

tff(c_1509,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_1508])).

tff(c_18,plain,(
    ! [B_25,A_19] :
      ( k1_funct_1(B_25,'#skF_2'(A_19,B_25)) != k1_funct_1(A_19,'#skF_2'(A_19,B_25))
      | r1_partfun1(A_19,B_25)
      | ~ r1_tarski(k1_relat_1(A_19),k1_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1516,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_18])).

tff(c_1521,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_32,c_53,c_28,c_171,c_238,c_1516])).

tff(c_1523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_1521])).

tff(c_1524,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1556,plain,(
    ! [A_288,B_289,C_290] :
      ( k1_relset_1(A_288,B_289,C_290) = k1_relat_1(C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1563,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1556])).

tff(c_1603,plain,(
    ! [A_296,B_297,C_298] :
      ( m1_subset_1(k1_relset_1(A_296,B_297,C_298),k1_zfmisc_1(A_296))
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1617,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_1603])).

tff(c_1623,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1617])).

tff(c_1549,plain,(
    ! [C_285,A_286,B_287] :
      ( r2_hidden(C_285,A_286)
      | ~ r2_hidden(C_285,B_287)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(A_286)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1730,plain,(
    ! [A_309,B_310,A_311] :
      ( r2_hidden('#skF_1'(A_309,B_310),A_311)
      | ~ m1_subset_1(A_309,k1_zfmisc_1(A_311))
      | r1_tarski(A_309,B_310) ) ),
    inference(resolution,[status(thm)],[c_6,c_1549])).

tff(c_1742,plain,(
    ! [A_312,A_313] :
      ( ~ m1_subset_1(A_312,k1_zfmisc_1(A_313))
      | r1_tarski(A_312,A_313) ) ),
    inference(resolution,[status(thm)],[c_1730,c_4])).

tff(c_1760,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1623,c_1742])).

tff(c_1525,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1564,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1556])).

tff(c_1671,plain,(
    ! [A_305,B_306] :
      ( k1_relset_1(A_305,A_305,B_306) = A_305
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k2_zfmisc_1(A_305,A_305)))
      | ~ v1_funct_2(B_306,A_305,A_305)
      | ~ v1_funct_1(B_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1681,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1671])).

tff(c_1688,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1564,c_1681])).

tff(c_36,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1527,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_36])).

tff(c_1566,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1563,c_1527])).

tff(c_1824,plain,(
    ! [B_324,C_325,A_326] :
      ( k1_funct_1(B_324,C_325) = k1_funct_1(A_326,C_325)
      | ~ r2_hidden(C_325,k1_relat_1(A_326))
      | ~ r1_partfun1(A_326,B_324)
      | ~ r1_tarski(k1_relat_1(A_326),k1_relat_1(B_324))
      | ~ v1_funct_1(B_324)
      | ~ v1_relat_1(B_324)
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1839,plain,(
    ! [B_324] :
      ( k1_funct_1(B_324,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_324)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_324))
      | ~ v1_funct_1(B_324)
      | ~ v1_relat_1(B_324)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1566,c_1824])).

tff(c_2498,plain,(
    ! [B_443] :
      ( k1_funct_1(B_443,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_443)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_443))
      | ~ v1_funct_1(B_443)
      | ~ v1_relat_1(B_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_32,c_1839])).

tff(c_2501,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_2498])).

tff(c_2507,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_28,c_1760,c_1525,c_2501])).

tff(c_2509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1524,c_2507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.21/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/1.98  
% 5.21/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/1.98  %$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.39/1.98  
% 5.39/1.98  %Foreground sorts:
% 5.39/1.98  
% 5.39/1.98  
% 5.39/1.98  %Background operators:
% 5.39/1.98  
% 5.39/1.98  
% 5.39/1.98  %Foreground operators:
% 5.39/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.39/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.39/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.39/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.39/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.39/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.39/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.39/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.39/1.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.39/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.39/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.39/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.39/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.39/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.39/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.39/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.39/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.39/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.39/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.39/1.98  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 5.39/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.39/1.98  
% 5.39/2.00  tff(f_96, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) <=> (![D]: (r2_hidden(D, k1_relset_1(A, A, B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_2)).
% 5.39/2.00  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.39/2.00  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.39/2.00  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.39/2.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.39/2.00  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.39/2.00  tff(f_77, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.39/2.00  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 5.39/2.00  tff(c_34, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.00  tff(c_55, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 5.39/2.00  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.00  tff(c_45, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.39/2.00  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_45])).
% 5.39/2.00  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.00  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.00  tff(c_53, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_45])).
% 5.39/2.00  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.00  tff(c_83, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.39/2.00  tff(c_90, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_83])).
% 5.39/2.00  tff(c_139, plain, (![A_65, B_66, C_67]: (m1_subset_1(k1_relset_1(A_65, B_66, C_67), k1_zfmisc_1(A_65)) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.39/2.00  tff(c_156, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_139])).
% 5.39/2.00  tff(c_163, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_156])).
% 5.39/2.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.39/2.00  tff(c_67, plain, (![C_50, A_51, B_52]: (r2_hidden(C_50, A_51) | ~r2_hidden(C_50, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.00  tff(c_113, plain, (![A_60, B_61, A_62]: (r2_hidden('#skF_1'(A_60, B_61), A_62) | ~m1_subset_1(A_60, k1_zfmisc_1(A_62)) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_6, c_67])).
% 5.39/2.00  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.39/2.00  tff(c_129, plain, (![A_60, A_62]: (~m1_subset_1(A_60, k1_zfmisc_1(A_62)) | r1_tarski(A_60, A_62))), inference(resolution, [status(thm)], [c_113, c_4])).
% 5.39/2.00  tff(c_171, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_163, c_129])).
% 5.39/2.00  tff(c_26, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.00  tff(c_91, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_83])).
% 5.39/2.00  tff(c_221, plain, (![A_78, B_79]: (k1_relset_1(A_78, A_78, B_79)=A_78 | ~m1_subset_1(B_79, k1_zfmisc_1(k2_zfmisc_1(A_78, A_78))) | ~v1_funct_2(B_79, A_78, A_78) | ~v1_funct_1(B_79))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.39/2.00  tff(c_231, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_221])).
% 5.39/2.00  tff(c_238, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_91, c_231])).
% 5.39/2.00  tff(c_280, plain, (![A_83, B_84]: (r2_hidden('#skF_2'(A_83, B_84), k1_relat_1(A_83)) | r1_partfun1(A_83, B_84) | ~r1_tarski(k1_relat_1(A_83), k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.39/2.00  tff(c_44, plain, (![D_38]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', D_38)=k1_funct_1('#skF_4', D_38) | ~r2_hidden(D_38, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.00  tff(c_96, plain, (![D_38]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', D_38)=k1_funct_1('#skF_4', D_38) | ~r2_hidden(D_38, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_44])).
% 5.39/2.00  tff(c_97, plain, (![D_38]: (k1_funct_1('#skF_5', D_38)=k1_funct_1('#skF_4', D_38) | ~r2_hidden(D_38, k1_relat_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_55, c_96])).
% 5.39/2.00  tff(c_284, plain, (![B_84]: (k1_funct_1('#skF_5', '#skF_2'('#skF_4', B_84))=k1_funct_1('#skF_4', '#skF_2'('#skF_4', B_84)) | r1_partfun1('#skF_4', B_84) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_280, c_97])).
% 5.39/2.00  tff(c_1499, plain, (![B_277]: (k1_funct_1('#skF_5', '#skF_2'('#skF_4', B_277))=k1_funct_1('#skF_4', '#skF_2'('#skF_4', B_277)) | r1_partfun1('#skF_4', B_277) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_277)) | ~v1_funct_1(B_277) | ~v1_relat_1(B_277))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_32, c_284])).
% 5.39/2.00  tff(c_1502, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_2'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_238, c_1499])).
% 5.39/2.00  tff(c_1508, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_2'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_28, c_171, c_1502])).
% 5.39/2.00  tff(c_1509, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_55, c_1508])).
% 5.39/2.00  tff(c_18, plain, (![B_25, A_19]: (k1_funct_1(B_25, '#skF_2'(A_19, B_25))!=k1_funct_1(A_19, '#skF_2'(A_19, B_25)) | r1_partfun1(A_19, B_25) | ~r1_tarski(k1_relat_1(A_19), k1_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.39/2.00  tff(c_1516, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1509, c_18])).
% 5.39/2.00  tff(c_1521, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_32, c_53, c_28, c_171, c_238, c_1516])).
% 5.39/2.00  tff(c_1523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_1521])).
% 5.39/2.00  tff(c_1524, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 5.39/2.00  tff(c_1556, plain, (![A_288, B_289, C_290]: (k1_relset_1(A_288, B_289, C_290)=k1_relat_1(C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.39/2.00  tff(c_1563, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1556])).
% 5.39/2.00  tff(c_1603, plain, (![A_296, B_297, C_298]: (m1_subset_1(k1_relset_1(A_296, B_297, C_298), k1_zfmisc_1(A_296)) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.39/2.00  tff(c_1617, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1563, c_1603])).
% 5.39/2.00  tff(c_1623, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1617])).
% 5.39/2.00  tff(c_1549, plain, (![C_285, A_286, B_287]: (r2_hidden(C_285, A_286) | ~r2_hidden(C_285, B_287) | ~m1_subset_1(B_287, k1_zfmisc_1(A_286)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.39/2.00  tff(c_1730, plain, (![A_309, B_310, A_311]: (r2_hidden('#skF_1'(A_309, B_310), A_311) | ~m1_subset_1(A_309, k1_zfmisc_1(A_311)) | r1_tarski(A_309, B_310))), inference(resolution, [status(thm)], [c_6, c_1549])).
% 5.39/2.00  tff(c_1742, plain, (![A_312, A_313]: (~m1_subset_1(A_312, k1_zfmisc_1(A_313)) | r1_tarski(A_312, A_313))), inference(resolution, [status(thm)], [c_1730, c_4])).
% 5.39/2.00  tff(c_1760, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1623, c_1742])).
% 5.39/2.00  tff(c_1525, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 5.39/2.00  tff(c_1564, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1556])).
% 5.39/2.00  tff(c_1671, plain, (![A_305, B_306]: (k1_relset_1(A_305, A_305, B_306)=A_305 | ~m1_subset_1(B_306, k1_zfmisc_1(k2_zfmisc_1(A_305, A_305))) | ~v1_funct_2(B_306, A_305, A_305) | ~v1_funct_1(B_306))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.39/2.00  tff(c_1681, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1671])).
% 5.39/2.00  tff(c_1688, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1564, c_1681])).
% 5.39/2.00  tff(c_36, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.39/2.00  tff(c_1527, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_36])).
% 5.39/2.00  tff(c_1566, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1563, c_1527])).
% 5.39/2.00  tff(c_1824, plain, (![B_324, C_325, A_326]: (k1_funct_1(B_324, C_325)=k1_funct_1(A_326, C_325) | ~r2_hidden(C_325, k1_relat_1(A_326)) | ~r1_partfun1(A_326, B_324) | ~r1_tarski(k1_relat_1(A_326), k1_relat_1(B_324)) | ~v1_funct_1(B_324) | ~v1_relat_1(B_324) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.39/2.00  tff(c_1839, plain, (![B_324]: (k1_funct_1(B_324, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_324) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_324)) | ~v1_funct_1(B_324) | ~v1_relat_1(B_324) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1566, c_1824])).
% 5.39/2.00  tff(c_2498, plain, (![B_443]: (k1_funct_1(B_443, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_443) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_443)) | ~v1_funct_1(B_443) | ~v1_relat_1(B_443))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_32, c_1839])).
% 5.39/2.00  tff(c_2501, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1688, c_2498])).
% 5.39/2.00  tff(c_2507, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_28, c_1760, c_1525, c_2501])).
% 5.39/2.00  tff(c_2509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1524, c_2507])).
% 5.39/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.00  
% 5.39/2.00  Inference rules
% 5.39/2.00  ----------------------
% 5.39/2.00  #Ref     : 2
% 5.39/2.00  #Sup     : 602
% 5.39/2.00  #Fact    : 0
% 5.39/2.00  #Define  : 0
% 5.39/2.00  #Split   : 40
% 5.39/2.00  #Chain   : 0
% 5.39/2.00  #Close   : 0
% 5.39/2.00  
% 5.39/2.00  Ordering : KBO
% 5.39/2.00  
% 5.39/2.00  Simplification rules
% 5.39/2.00  ----------------------
% 5.39/2.00  #Subsume      : 223
% 5.39/2.00  #Demod        : 183
% 5.39/2.00  #Tautology    : 60
% 5.39/2.00  #SimpNegUnit  : 5
% 5.39/2.00  #BackRed      : 8
% 5.39/2.00  
% 5.39/2.00  #Partial instantiations: 0
% 5.39/2.00  #Strategies tried      : 1
% 5.39/2.00  
% 5.39/2.00  Timing (in seconds)
% 5.39/2.00  ----------------------
% 5.39/2.00  Preprocessing        : 0.31
% 5.39/2.00  Parsing              : 0.16
% 5.39/2.00  CNF conversion       : 0.02
% 5.39/2.00  Main loop            : 0.88
% 5.39/2.00  Inferencing          : 0.29
% 5.39/2.00  Reduction            : 0.25
% 5.39/2.00  Demodulation         : 0.17
% 5.39/2.00  BG Simplification    : 0.03
% 5.39/2.00  Subsumption          : 0.25
% 5.39/2.00  Abstraction          : 0.04
% 5.39/2.00  MUC search           : 0.00
% 5.39/2.00  Cooper               : 0.00
% 5.39/2.00  Total                : 1.23
% 5.39/2.00  Index Insertion      : 0.00
% 5.39/2.00  Index Deletion       : 0.00
% 5.39/2.00  Index Matching       : 0.00
% 5.39/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
