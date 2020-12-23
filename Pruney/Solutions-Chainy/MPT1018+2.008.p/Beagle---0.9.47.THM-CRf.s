%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:46 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 241 expanded)
%              Number of leaves         :   29 ( 103 expanded)
%              Depth                    :    8
%              Number of atoms          :  173 ( 910 expanded)
%              Number of equality atoms :   57 ( 247 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_378,plain,(
    ! [D_97,C_98,B_99,A_100] :
      ( k1_funct_1(k2_funct_1(D_97),k1_funct_1(D_97,C_98)) = C_98
      | k1_xboole_0 = B_99
      | ~ r2_hidden(C_98,A_100)
      | ~ v2_funct_1(D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99)))
      | ~ v1_funct_2(D_97,A_100,B_99)
      | ~ v1_funct_1(D_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_463,plain,(
    ! [D_120,B_121] :
      ( k1_funct_1(k2_funct_1(D_120),k1_funct_1(D_120,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_121
      | ~ v2_funct_1(D_120)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_121)))
      | ~ v1_funct_2(D_120,'#skF_3',B_121)
      | ~ v1_funct_1(D_120) ) ),
    inference(resolution,[status(thm)],[c_28,c_378])).

tff(c_468,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_463])).

tff(c_472,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_468])).

tff(c_473,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_477,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_2])).

tff(c_24,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [C_35,A_36,B_37] :
      ( r2_hidden(C_35,A_36)
      | ~ r2_hidden(C_35,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_6',A_38)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_38)) ) ),
    inference(resolution,[status(thm)],[c_28,c_75])).

tff(c_87,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_6',B_7)
      | ~ r1_tarski('#skF_3',B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_26,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_206,plain,(
    ! [D_76,C_77,B_78,A_79] :
      ( k1_funct_1(k2_funct_1(D_76),k1_funct_1(D_76,C_77)) = C_77
      | k1_xboole_0 = B_78
      | ~ r2_hidden(C_77,A_79)
      | ~ v2_funct_1(D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78)))
      | ~ v1_funct_2(D_76,A_79,B_78)
      | ~ v1_funct_1(D_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_250,plain,(
    ! [D_87,B_88] :
      ( k1_funct_1(k2_funct_1(D_87),k1_funct_1(D_87,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_88
      | ~ v2_funct_1(D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_88)))
      | ~ v1_funct_2(D_87,'#skF_3',B_88)
      | ~ v1_funct_1(D_87) ) ),
    inference(resolution,[status(thm)],[c_30,c_206])).

tff(c_255,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_250])).

tff(c_259,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_26,c_255])).

tff(c_260,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_264,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_2])).

tff(c_92,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_5',A_40)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_30,c_75])).

tff(c_97,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_5',B_7)
      | ~ r1_tarski('#skF_3',B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_54,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_165,plain,(
    ! [C_62,B_63,A_64] :
      ( C_62 = B_63
      | k1_funct_1(A_64,C_62) != k1_funct_1(A_64,B_63)
      | ~ r2_hidden(C_62,k1_relat_1(A_64))
      | ~ r2_hidden(B_63,k1_relat_1(A_64))
      | ~ v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_171,plain,(
    ! [B_63] :
      ( B_63 = '#skF_5'
      | k1_funct_1('#skF_4',B_63) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_63,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_165])).

tff(c_175,plain,(
    ! [B_63] :
      ( B_63 = '#skF_5'
      | k1_funct_1('#skF_4',B_63) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_63,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_38,c_32,c_171])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_182,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_97,c_178])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_182])).

tff(c_287,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_288,plain,(
    ! [D_89,B_90] :
      ( k1_funct_1(k2_funct_1(D_89),k1_funct_1(D_89,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_90
      | ~ v2_funct_1(D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_90)))
      | ~ v1_funct_2(D_89,'#skF_3',B_90)
      | ~ v1_funct_1(D_89) ) ),
    inference(resolution,[status(thm)],[c_28,c_206])).

tff(c_293,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_288])).

tff(c_297,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_293])).

tff(c_298,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_297])).

tff(c_286,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_307,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_286])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_307])).

tff(c_311,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_173,plain,(
    ! [C_62] :
      ( C_62 = '#skF_5'
      | k1_funct_1('#skF_4',C_62) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_62,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_165])).

tff(c_177,plain,(
    ! [C_62] :
      ( C_62 = '#skF_5'
      | k1_funct_1('#skF_4',C_62) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_62,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_38,c_32,c_173])).

tff(c_317,plain,(
    ! [C_91] :
      ( C_91 = '#skF_5'
      | k1_funct_1('#skF_4',C_91) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_91,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_177])).

tff(c_344,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_87,c_317])).

tff(c_363,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_344])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_363])).

tff(c_512,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_511,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_523,plain,(
    ! [D_126,B_127] :
      ( k1_funct_1(k2_funct_1(D_126),k1_funct_1(D_126,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_127
      | ~ v2_funct_1(D_126)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_127)))
      | ~ v1_funct_2(D_126,'#skF_3',B_127)
      | ~ v1_funct_1(D_126) ) ),
    inference(resolution,[status(thm)],[c_30,c_378])).

tff(c_528,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_523])).

tff(c_532,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_511,c_26,c_528])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_24,c_532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.47  
% 3.10/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.47  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.10/1.47  
% 3.10/1.47  %Foreground sorts:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Background operators:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Foreground operators:
% 3.10/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.10/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.10/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.10/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.47  
% 3.28/1.49  tff(f_89, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 3.28/1.49  tff(f_71, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.28/1.49  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.28/1.49  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.28/1.49  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.28/1.49  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.28/1.49  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 3.28/1.49  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.49  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.49  tff(c_32, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.49  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.49  tff(c_28, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.49  tff(c_378, plain, (![D_97, C_98, B_99, A_100]: (k1_funct_1(k2_funct_1(D_97), k1_funct_1(D_97, C_98))=C_98 | k1_xboole_0=B_99 | ~r2_hidden(C_98, A_100) | ~v2_funct_1(D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))) | ~v1_funct_2(D_97, A_100, B_99) | ~v1_funct_1(D_97))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.49  tff(c_463, plain, (![D_120, B_121]: (k1_funct_1(k2_funct_1(D_120), k1_funct_1(D_120, '#skF_6'))='#skF_6' | k1_xboole_0=B_121 | ~v2_funct_1(D_120) | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_121))) | ~v1_funct_2(D_120, '#skF_3', B_121) | ~v1_funct_1(D_120))), inference(resolution, [status(thm)], [c_28, c_378])).
% 3.28/1.49  tff(c_468, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_463])).
% 3.28/1.49  tff(c_472, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_468])).
% 3.28/1.49  tff(c_473, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_472])).
% 3.28/1.49  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.28/1.49  tff(c_477, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_2])).
% 3.28/1.49  tff(c_24, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.49  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.49  tff(c_75, plain, (![C_35, A_36, B_37]: (r2_hidden(C_35, A_36) | ~r2_hidden(C_35, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.49  tff(c_82, plain, (![A_38]: (r2_hidden('#skF_6', A_38) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_38)))), inference(resolution, [status(thm)], [c_28, c_75])).
% 3.28/1.49  tff(c_87, plain, (![B_7]: (r2_hidden('#skF_6', B_7) | ~r1_tarski('#skF_3', B_7))), inference(resolution, [status(thm)], [c_8, c_82])).
% 3.28/1.49  tff(c_26, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.49  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.49  tff(c_206, plain, (![D_76, C_77, B_78, A_79]: (k1_funct_1(k2_funct_1(D_76), k1_funct_1(D_76, C_77))=C_77 | k1_xboole_0=B_78 | ~r2_hidden(C_77, A_79) | ~v2_funct_1(D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))) | ~v1_funct_2(D_76, A_79, B_78) | ~v1_funct_1(D_76))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.49  tff(c_250, plain, (![D_87, B_88]: (k1_funct_1(k2_funct_1(D_87), k1_funct_1(D_87, '#skF_5'))='#skF_5' | k1_xboole_0=B_88 | ~v2_funct_1(D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_88))) | ~v1_funct_2(D_87, '#skF_3', B_88) | ~v1_funct_1(D_87))), inference(resolution, [status(thm)], [c_30, c_206])).
% 3.28/1.49  tff(c_255, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_250])).
% 3.28/1.49  tff(c_259, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_26, c_255])).
% 3.28/1.49  tff(c_260, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_259])).
% 3.28/1.49  tff(c_264, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_2])).
% 3.28/1.49  tff(c_92, plain, (![A_40]: (r2_hidden('#skF_5', A_40) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_30, c_75])).
% 3.28/1.49  tff(c_97, plain, (![B_7]: (r2_hidden('#skF_5', B_7) | ~r1_tarski('#skF_3', B_7))), inference(resolution, [status(thm)], [c_8, c_92])).
% 3.28/1.49  tff(c_54, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.28/1.49  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_54])).
% 3.28/1.49  tff(c_165, plain, (![C_62, B_63, A_64]: (C_62=B_63 | k1_funct_1(A_64, C_62)!=k1_funct_1(A_64, B_63) | ~r2_hidden(C_62, k1_relat_1(A_64)) | ~r2_hidden(B_63, k1_relat_1(A_64)) | ~v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.49  tff(c_171, plain, (![B_63]: (B_63='#skF_5' | k1_funct_1('#skF_4', B_63)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_63, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_165])).
% 3.28/1.49  tff(c_175, plain, (![B_63]: (B_63='#skF_5' | k1_funct_1('#skF_4', B_63)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_63, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_38, c_32, c_171])).
% 3.28/1.49  tff(c_178, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_175])).
% 3.28/1.49  tff(c_182, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_97, c_178])).
% 3.28/1.49  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_182])).
% 3.28/1.49  tff(c_287, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_259])).
% 3.28/1.49  tff(c_288, plain, (![D_89, B_90]: (k1_funct_1(k2_funct_1(D_89), k1_funct_1(D_89, '#skF_6'))='#skF_6' | k1_xboole_0=B_90 | ~v2_funct_1(D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_90))) | ~v1_funct_2(D_89, '#skF_3', B_90) | ~v1_funct_1(D_89))), inference(resolution, [status(thm)], [c_28, c_206])).
% 3.28/1.49  tff(c_293, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_288])).
% 3.28/1.49  tff(c_297, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_293])).
% 3.28/1.49  tff(c_298, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_287, c_297])).
% 3.28/1.49  tff(c_286, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_259])).
% 3.28/1.49  tff(c_307, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_286])).
% 3.28/1.49  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_307])).
% 3.28/1.49  tff(c_311, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_175])).
% 3.28/1.49  tff(c_173, plain, (![C_62]: (C_62='#skF_5' | k1_funct_1('#skF_4', C_62)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_62, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_165])).
% 3.28/1.49  tff(c_177, plain, (![C_62]: (C_62='#skF_5' | k1_funct_1('#skF_4', C_62)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_62, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_38, c_32, c_173])).
% 3.28/1.49  tff(c_317, plain, (![C_91]: (C_91='#skF_5' | k1_funct_1('#skF_4', C_91)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_91, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_177])).
% 3.28/1.49  tff(c_344, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_87, c_317])).
% 3.28/1.49  tff(c_363, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_24, c_344])).
% 3.28/1.49  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_477, c_363])).
% 3.28/1.49  tff(c_512, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_472])).
% 3.28/1.49  tff(c_511, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_472])).
% 3.28/1.49  tff(c_523, plain, (![D_126, B_127]: (k1_funct_1(k2_funct_1(D_126), k1_funct_1(D_126, '#skF_5'))='#skF_5' | k1_xboole_0=B_127 | ~v2_funct_1(D_126) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_127))) | ~v1_funct_2(D_126, '#skF_3', B_127) | ~v1_funct_1(D_126))), inference(resolution, [status(thm)], [c_30, c_378])).
% 3.28/1.49  tff(c_528, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_523])).
% 3.28/1.49  tff(c_532, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_511, c_26, c_528])).
% 3.28/1.49  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_512, c_24, c_532])).
% 3.28/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.49  
% 3.28/1.49  Inference rules
% 3.28/1.49  ----------------------
% 3.28/1.49  #Ref     : 1
% 3.28/1.49  #Sup     : 106
% 3.28/1.49  #Fact    : 0
% 3.28/1.49  #Define  : 0
% 3.28/1.49  #Split   : 4
% 3.28/1.49  #Chain   : 0
% 3.28/1.49  #Close   : 0
% 3.28/1.49  
% 3.28/1.49  Ordering : KBO
% 3.28/1.49  
% 3.28/1.49  Simplification rules
% 3.28/1.49  ----------------------
% 3.28/1.49  #Subsume      : 3
% 3.28/1.49  #Demod        : 61
% 3.28/1.49  #Tautology    : 22
% 3.28/1.49  #SimpNegUnit  : 4
% 3.28/1.49  #BackRed      : 25
% 3.28/1.49  
% 3.28/1.49  #Partial instantiations: 0
% 3.28/1.49  #Strategies tried      : 1
% 3.28/1.49  
% 3.28/1.49  Timing (in seconds)
% 3.28/1.49  ----------------------
% 3.28/1.49  Preprocessing        : 0.33
% 3.28/1.49  Parsing              : 0.18
% 3.28/1.49  CNF conversion       : 0.02
% 3.28/1.49  Main loop            : 0.36
% 3.28/1.49  Inferencing          : 0.13
% 3.28/1.49  Reduction            : 0.10
% 3.28/1.49  Demodulation         : 0.07
% 3.28/1.49  BG Simplification    : 0.02
% 3.28/1.49  Subsumption          : 0.08
% 3.28/1.49  Abstraction          : 0.02
% 3.28/1.49  MUC search           : 0.00
% 3.28/1.49  Cooper               : 0.00
% 3.28/1.49  Total                : 0.73
% 3.28/1.49  Index Insertion      : 0.00
% 3.28/1.49  Index Deletion       : 0.00
% 3.28/1.49  Index Matching       : 0.00
% 3.28/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
