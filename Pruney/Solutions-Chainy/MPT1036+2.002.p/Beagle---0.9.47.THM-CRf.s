%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:00 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 297 expanded)
%              Number of leaves         :   29 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  166 ( 967 expanded)
%              Number of equality atoms :   33 ( 156 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_63,axiom,(
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

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_43,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_52,plain,(
    ! [C_35,A_36,B_37] :
      ( v4_relat_1(C_35,A_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,
    ( k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_61,plain,(
    ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_51,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_43])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_79,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_98,plain,(
    ! [A_50,B_51] :
      ( k1_relset_1(A_50,A_50,B_51) = A_50
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_zfmisc_1(A_50,A_50)))
      | ~ v1_funct_2(B_51,A_50,A_50)
      | ~ v1_funct_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_98])).

tff(c_110,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_87,c_104])).

tff(c_143,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),k1_relat_1(A_54))
      | r1_partfun1(A_54,B_55)
      | ~ r1_tarski(k1_relat_1(A_54),k1_relat_1(B_55))
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_79])).

tff(c_42,plain,(
    ! [D_31] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_31) = k1_funct_1('#skF_4',D_31)
      | ~ r2_hidden(D_31,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_77,plain,(
    ! [D_31] :
      ( k1_funct_1('#skF_3',D_31) = k1_funct_1('#skF_4',D_31)
      | ~ r2_hidden(D_31,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_42])).

tff(c_88,plain,(
    ! [D_31] :
      ( k1_funct_1('#skF_3',D_31) = k1_funct_1('#skF_4',D_31)
      | ~ r2_hidden(D_31,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_77])).

tff(c_147,plain,(
    ! [B_55] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_55)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_55))
      | r1_partfun1('#skF_3',B_55)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_55))
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_88])).

tff(c_169,plain,(
    ! [B_62] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_62)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_62))
      | r1_partfun1('#skF_3',B_62)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_62))
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30,c_147])).

tff(c_172,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_169])).

tff(c_177,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_26,c_172])).

tff(c_178,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_177])).

tff(c_182,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_185,plain,
    ( ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_59,c_185])).

tff(c_191,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_190,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_212,plain,(
    ! [B_64,A_65] :
      ( k1_funct_1(B_64,'#skF_1'(A_65,B_64)) != k1_funct_1(A_65,'#skF_1'(A_65,B_64))
      | r1_partfun1(A_65,B_64)
      | ~ r1_tarski(k1_relat_1(A_65),k1_relat_1(B_64))
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_214,plain,
    ( r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_212])).

tff(c_217,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30,c_51,c_26,c_191,c_110,c_214])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_217])).

tff(c_220,plain,(
    k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_221,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_239,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_247,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_239])).

tff(c_258,plain,(
    ! [A_76,B_77] :
      ( k1_relset_1(A_76,A_76,B_77) = A_76
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_zfmisc_1(A_76,A_76)))
      | ~ v1_funct_2(B_77,A_76,A_76)
      | ~ v1_funct_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_264,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_258])).

tff(c_270,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_247,c_264])).

tff(c_246,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_34,plain,
    ( r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3'))
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_223,plain,(
    r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_34])).

tff(c_248,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_223])).

tff(c_330,plain,(
    ! [B_86,C_87,A_88] :
      ( k1_funct_1(B_86,C_87) = k1_funct_1(A_88,C_87)
      | ~ r2_hidden(C_87,k1_relat_1(A_88))
      | ~ r1_partfun1(A_88,B_86)
      | ~ r1_tarski(k1_relat_1(A_88),k1_relat_1(B_86))
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_336,plain,(
    ! [B_86] :
      ( k1_funct_1(B_86,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_86)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_86))
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_248,c_330])).

tff(c_357,plain,(
    ! [B_90] :
      ( k1_funct_1(B_90,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_90)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_90))
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30,c_336])).

tff(c_360,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_357])).

tff(c_365,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_26,c_221,c_360])).

tff(c_366,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_365])).

tff(c_372,plain,
    ( ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_366])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_59,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.24/1.30  
% 2.24/1.30  %Foreground sorts:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Background operators:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Foreground operators:
% 2.24/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.24/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.24/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.30  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.24/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.30  
% 2.54/1.32  tff(f_90, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) <=> (![D]: (r2_hidden(D, k1_relset_1(A, A, B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_2)).
% 2.54/1.32  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.54/1.32  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.54/1.32  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.54/1.32  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.54/1.32  tff(f_71, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.54/1.32  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 2.54/1.32  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.32  tff(c_43, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.32  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_43])).
% 2.54/1.32  tff(c_52, plain, (![C_35, A_36, B_37]: (v4_relat_1(C_35, A_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.32  tff(c_59, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.54/1.32  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.32  tff(c_32, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.32  tff(c_61, plain, (~r1_partfun1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 2.54/1.32  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.32  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.32  tff(c_51, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_43])).
% 2.54/1.32  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.32  tff(c_24, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.32  tff(c_79, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.32  tff(c_87, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_79])).
% 2.54/1.32  tff(c_98, plain, (![A_50, B_51]: (k1_relset_1(A_50, A_50, B_51)=A_50 | ~m1_subset_1(B_51, k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))) | ~v1_funct_2(B_51, A_50, A_50) | ~v1_funct_1(B_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.54/1.32  tff(c_104, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_98])).
% 2.54/1.32  tff(c_110, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_87, c_104])).
% 2.54/1.32  tff(c_143, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), k1_relat_1(A_54)) | r1_partfun1(A_54, B_55) | ~r1_tarski(k1_relat_1(A_54), k1_relat_1(B_55)) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.54/1.32  tff(c_86, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_79])).
% 2.54/1.32  tff(c_42, plain, (![D_31]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_31)=k1_funct_1('#skF_4', D_31) | ~r2_hidden(D_31, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.32  tff(c_77, plain, (![D_31]: (k1_funct_1('#skF_3', D_31)=k1_funct_1('#skF_4', D_31) | ~r2_hidden(D_31, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_61, c_42])).
% 2.54/1.32  tff(c_88, plain, (![D_31]: (k1_funct_1('#skF_3', D_31)=k1_funct_1('#skF_4', D_31) | ~r2_hidden(D_31, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_77])).
% 2.54/1.32  tff(c_147, plain, (![B_55]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_55))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_55)) | r1_partfun1('#skF_3', B_55) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_55)) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_143, c_88])).
% 2.54/1.32  tff(c_169, plain, (![B_62]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_62))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_62)) | r1_partfun1('#skF_3', B_62) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_62)) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30, c_147])).
% 2.54/1.32  tff(c_172, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_110, c_169])).
% 2.54/1.32  tff(c_177, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_26, c_172])).
% 2.54/1.32  tff(c_178, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_61, c_177])).
% 2.54/1.32  tff(c_182, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_178])).
% 2.54/1.32  tff(c_185, plain, (~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_182])).
% 2.54/1.32  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_59, c_185])).
% 2.54/1.32  tff(c_191, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 2.54/1.32  tff(c_190, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_178])).
% 2.54/1.32  tff(c_212, plain, (![B_64, A_65]: (k1_funct_1(B_64, '#skF_1'(A_65, B_64))!=k1_funct_1(A_65, '#skF_1'(A_65, B_64)) | r1_partfun1(A_65, B_64) | ~r1_tarski(k1_relat_1(A_65), k1_relat_1(B_64)) | ~v1_funct_1(B_64) | ~v1_relat_1(B_64) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.54/1.32  tff(c_214, plain, (r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_190, c_212])).
% 2.54/1.32  tff(c_217, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30, c_51, c_26, c_191, c_110, c_214])).
% 2.54/1.32  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_217])).
% 2.54/1.32  tff(c_220, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.32  tff(c_221, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.32  tff(c_239, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.32  tff(c_247, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_239])).
% 2.54/1.32  tff(c_258, plain, (![A_76, B_77]: (k1_relset_1(A_76, A_76, B_77)=A_76 | ~m1_subset_1(B_77, k1_zfmisc_1(k2_zfmisc_1(A_76, A_76))) | ~v1_funct_2(B_77, A_76, A_76) | ~v1_funct_1(B_77))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.54/1.32  tff(c_264, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_258])).
% 2.54/1.32  tff(c_270, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_247, c_264])).
% 2.54/1.32  tff(c_246, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_239])).
% 2.54/1.32  tff(c_34, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3')) | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.32  tff(c_223, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_34])).
% 2.54/1.32  tff(c_248, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_223])).
% 2.54/1.32  tff(c_330, plain, (![B_86, C_87, A_88]: (k1_funct_1(B_86, C_87)=k1_funct_1(A_88, C_87) | ~r2_hidden(C_87, k1_relat_1(A_88)) | ~r1_partfun1(A_88, B_86) | ~r1_tarski(k1_relat_1(A_88), k1_relat_1(B_86)) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.54/1.32  tff(c_336, plain, (![B_86]: (k1_funct_1(B_86, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_86) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_86)) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_248, c_330])).
% 2.54/1.32  tff(c_357, plain, (![B_90]: (k1_funct_1(B_90, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_90) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_90)) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30, c_336])).
% 2.54/1.32  tff(c_360, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_270, c_357])).
% 2.54/1.32  tff(c_365, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_26, c_221, c_360])).
% 2.54/1.32  tff(c_366, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_220, c_365])).
% 2.54/1.32  tff(c_372, plain, (~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_366])).
% 2.54/1.32  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_59, c_372])).
% 2.54/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.32  
% 2.54/1.32  Inference rules
% 2.54/1.32  ----------------------
% 2.54/1.32  #Ref     : 2
% 2.54/1.32  #Sup     : 67
% 2.54/1.32  #Fact    : 0
% 2.54/1.32  #Define  : 0
% 2.54/1.32  #Split   : 4
% 2.54/1.32  #Chain   : 0
% 2.54/1.32  #Close   : 0
% 2.54/1.32  
% 2.54/1.32  Ordering : KBO
% 2.54/1.32  
% 2.54/1.32  Simplification rules
% 2.54/1.32  ----------------------
% 2.54/1.32  #Subsume      : 4
% 2.54/1.32  #Demod        : 89
% 2.54/1.32  #Tautology    : 30
% 2.54/1.32  #SimpNegUnit  : 5
% 2.54/1.32  #BackRed      : 4
% 2.54/1.32  
% 2.54/1.32  #Partial instantiations: 0
% 2.54/1.32  #Strategies tried      : 1
% 2.54/1.32  
% 2.54/1.32  Timing (in seconds)
% 2.54/1.32  ----------------------
% 2.54/1.32  Preprocessing        : 0.31
% 2.54/1.32  Parsing              : 0.16
% 2.54/1.32  CNF conversion       : 0.02
% 2.54/1.32  Main loop            : 0.25
% 2.54/1.32  Inferencing          : 0.10
% 2.54/1.32  Reduction            : 0.08
% 2.54/1.32  Demodulation         : 0.05
% 2.54/1.32  BG Simplification    : 0.02
% 2.54/1.32  Subsumption          : 0.03
% 2.54/1.32  Abstraction          : 0.01
% 2.54/1.32  MUC search           : 0.00
% 2.54/1.32  Cooper               : 0.00
% 2.54/1.32  Total                : 0.59
% 2.54/1.32  Index Insertion      : 0.00
% 2.54/1.32  Index Deletion       : 0.00
% 2.54/1.32  Index Matching       : 0.00
% 2.54/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
