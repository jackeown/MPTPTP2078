%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:27 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  113 (1391 expanded)
%              Number of leaves         :   34 ( 495 expanded)
%              Depth                    :   19
%              Number of atoms          :  201 (4638 expanded)
%              Number of equality atoms :   76 (2057 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_88,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_92,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_88])).

tff(c_44,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_93,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_44])).

tff(c_259,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden('#skF_1'(A_91,B_92,C_93),B_92)
      | k2_relset_1(A_91,B_92,C_93) = B_92
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_261,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_259])).

tff(c_263,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_261])).

tff(c_264,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_263])).

tff(c_54,plain,(
    ! [D_40] :
      ( r2_hidden('#skF_6'(D_40),'#skF_3')
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_104,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_108,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_104])).

tff(c_165,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_82,B_81,C_83) = A_82
      | ~ v1_funct_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_168,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_165])).

tff(c_171,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_108,c_168])).

tff(c_172,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    ! [D_40] :
      ( k1_funct_1('#skF_5','#skF_6'(D_40)) = D_40
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_131,plain,(
    ! [B_72,A_73] :
      ( r2_hidden(k4_tarski(B_72,k1_funct_1(A_73,B_72)),A_73)
      | ~ r2_hidden(B_72,k1_relat_1(A_73))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski('#skF_6'(D_40),D_40),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_40),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_131])).

tff(c_143,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski('#skF_6'(D_40),D_40),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_40),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_50,c_140])).

tff(c_174,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski('#skF_6'(D_40),D_40),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_40),'#skF_3')
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_143])).

tff(c_265,plain,(
    ! [E_94,A_95,B_96,C_97] :
      ( ~ r2_hidden(k4_tarski(E_94,'#skF_1'(A_95,B_96,C_97)),C_97)
      | k2_relset_1(A_95,B_96,C_97) = B_96
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_286,plain,(
    ! [A_98,B_99] :
      ( k2_relset_1(A_98,B_99,'#skF_5') = B_99
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_98,B_99,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_98,B_99,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_174,c_265])).

tff(c_295,plain,(
    ! [A_100,B_101] :
      ( k2_relset_1(A_100,B_101,'#skF_5') = B_101
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ r2_hidden('#skF_1'(A_100,B_101,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_286])).

tff(c_298,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_295])).

tff(c_301,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_92,c_298])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_301])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_34,plain,(
    ! [C_36,A_34] :
      ( k1_xboole_0 = C_36
      | ~ v1_funct_2(C_36,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_373,plain,(
    ! [C_114,A_115] :
      ( C_114 = '#skF_4'
      | ~ v1_funct_2(C_114,A_115,'#skF_4')
      | A_115 = '#skF_4'
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_304,c_304,c_304,c_34])).

tff(c_376,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_373])).

tff(c_379,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_376])).

tff(c_380,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_305,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_394,plain,(
    k1_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_305])).

tff(c_400,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_48])).

tff(c_395,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_108])).

tff(c_399,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_46])).

tff(c_40,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_465,plain,(
    ! [B_126,C_127] :
      ( k1_relset_1('#skF_4',B_126,C_127) = '#skF_4'
      | ~ v1_funct_2(C_127,'#skF_4',B_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_126))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_304,c_304,c_304,c_40])).

tff(c_468,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_399,c_465])).

tff(c_471,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_395,c_468])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_471])).

tff(c_474,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_363,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_hidden('#skF_1'(A_111,B_112,C_113),B_112)
      | k2_relset_1(A_111,B_112,C_113) = B_112
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_365,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_363])).

tff(c_367,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_365])).

tff(c_368,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_367])).

tff(c_477,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_368])).

tff(c_482,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_93])).

tff(c_483,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_474,c_92])).

tff(c_486,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_46])).

tff(c_484,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_80])).

tff(c_488,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_50])).

tff(c_18,plain,(
    ! [A_8,B_11] :
      ( k1_funct_1(A_8,B_11) = k1_xboole_0
      | r2_hidden(B_11,k1_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_314,plain,(
    ! [A_8,B_11] :
      ( k1_funct_1(A_8,B_11) = '#skF_4'
      | r2_hidden(B_11,k1_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_18])).

tff(c_579,plain,(
    ! [D_137] :
      ( r2_hidden(k4_tarski('#skF_6'(D_137),D_137),'#skF_4')
      | ~ r2_hidden('#skF_6'(D_137),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_137,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_474,c_143])).

tff(c_28,plain,(
    ! [E_31,A_21,B_22,C_23] :
      ( ~ r2_hidden(k4_tarski(E_31,'#skF_1'(A_21,B_22,C_23)),C_23)
      | k2_relset_1(A_21,B_22,C_23) = B_22
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_622,plain,(
    ! [A_150,B_151] :
      ( k2_relset_1(A_150,B_151,'#skF_4') = B_151
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_150,B_151,'#skF_4')),k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_150,B_151,'#skF_4'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_579,c_28])).

tff(c_625,plain,(
    ! [A_150,B_151] :
      ( k2_relset_1(A_150,B_151,'#skF_4') = B_151
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ r2_hidden('#skF_1'(A_150,B_151,'#skF_4'),'#skF_4')
      | k1_funct_1('#skF_4','#skF_6'('#skF_1'(A_150,B_151,'#skF_4'))) = '#skF_4'
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_314,c_622])).

tff(c_651,plain,(
    ! [A_164,B_165] :
      ( k2_relset_1(A_164,B_165,'#skF_4') = B_165
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ r2_hidden('#skF_1'(A_164,B_165,'#skF_4'),'#skF_4')
      | k1_funct_1('#skF_4','#skF_6'('#skF_1'(A_164,B_165,'#skF_4'))) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_488,c_625])).

tff(c_654,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_4'),'#skF_4')
    | k1_funct_1('#skF_4','#skF_6'('#skF_1'('#skF_3','#skF_4','#skF_4'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_486,c_651])).

tff(c_657,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_funct_1('#skF_4','#skF_6'('#skF_1'('#skF_3','#skF_4','#skF_4'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_483,c_654])).

tff(c_658,plain,(
    k1_funct_1('#skF_4','#skF_6'('#skF_1'('#skF_3','#skF_4','#skF_4'))) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_657])).

tff(c_485,plain,(
    ! [D_40] :
      ( k1_funct_1('#skF_4','#skF_6'(D_40)) = D_40
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_52])).

tff(c_662,plain,
    ( '#skF_1'('#skF_3','#skF_4','#skF_4') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_485])).

tff(c_675,plain,(
    '#skF_1'('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_662])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_372,plain,(
    ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_368,c_20])).

tff(c_476,plain,(
    ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_372])).

tff(c_685,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_476])).

tff(c_689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_685])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:48:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.49  
% 3.07/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.49  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 3.07/1.49  
% 3.07/1.49  %Foreground sorts:
% 3.07/1.49  
% 3.07/1.49  
% 3.07/1.49  %Background operators:
% 3.07/1.49  
% 3.07/1.49  
% 3.07/1.49  %Foreground operators:
% 3.07/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.07/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.07/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.07/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.07/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.49  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.07/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.49  
% 3.23/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.51  tff(f_120, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.23/1.51  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.23/1.51  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 3.23/1.51  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.23/1.52  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.23/1.52  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.23/1.52  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.23/1.52  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 3.23/1.52  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.23/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.52  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.52  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.52  tff(c_88, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.52  tff(c_92, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_88])).
% 3.23/1.52  tff(c_44, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.52  tff(c_93, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_44])).
% 3.23/1.52  tff(c_259, plain, (![A_91, B_92, C_93]: (r2_hidden('#skF_1'(A_91, B_92, C_93), B_92) | k2_relset_1(A_91, B_92, C_93)=B_92 | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.52  tff(c_261, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_259])).
% 3.23/1.52  tff(c_263, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_261])).
% 3.23/1.52  tff(c_264, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_93, c_263])).
% 3.23/1.52  tff(c_54, plain, (![D_40]: (r2_hidden('#skF_6'(D_40), '#skF_3') | ~r2_hidden(D_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.52  tff(c_104, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.23/1.52  tff(c_108, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_104])).
% 3.23/1.52  tff(c_165, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_relset_1(A_82, B_81, C_83)=A_82 | ~v1_funct_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.52  tff(c_168, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_165])).
% 3.23/1.52  tff(c_171, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_108, c_168])).
% 3.23/1.52  tff(c_172, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_171])).
% 3.23/1.52  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.52  tff(c_74, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.52  tff(c_77, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_74])).
% 3.23/1.52  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77])).
% 3.23/1.52  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.52  tff(c_52, plain, (![D_40]: (k1_funct_1('#skF_5', '#skF_6'(D_40))=D_40 | ~r2_hidden(D_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.52  tff(c_131, plain, (![B_72, A_73]: (r2_hidden(k4_tarski(B_72, k1_funct_1(A_73, B_72)), A_73) | ~r2_hidden(B_72, k1_relat_1(A_73)) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.52  tff(c_140, plain, (![D_40]: (r2_hidden(k4_tarski('#skF_6'(D_40), D_40), '#skF_5') | ~r2_hidden('#skF_6'(D_40), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_40, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_131])).
% 3.23/1.52  tff(c_143, plain, (![D_40]: (r2_hidden(k4_tarski('#skF_6'(D_40), D_40), '#skF_5') | ~r2_hidden('#skF_6'(D_40), k1_relat_1('#skF_5')) | ~r2_hidden(D_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_50, c_140])).
% 3.23/1.52  tff(c_174, plain, (![D_40]: (r2_hidden(k4_tarski('#skF_6'(D_40), D_40), '#skF_5') | ~r2_hidden('#skF_6'(D_40), '#skF_3') | ~r2_hidden(D_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_143])).
% 3.23/1.52  tff(c_265, plain, (![E_94, A_95, B_96, C_97]: (~r2_hidden(k4_tarski(E_94, '#skF_1'(A_95, B_96, C_97)), C_97) | k2_relset_1(A_95, B_96, C_97)=B_96 | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.52  tff(c_286, plain, (![A_98, B_99]: (k2_relset_1(A_98, B_99, '#skF_5')=B_99 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~r2_hidden('#skF_6'('#skF_1'(A_98, B_99, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_98, B_99, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_174, c_265])).
% 3.23/1.52  tff(c_295, plain, (![A_100, B_101]: (k2_relset_1(A_100, B_101, '#skF_5')=B_101 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~r2_hidden('#skF_1'(A_100, B_101, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_286])).
% 3.23/1.52  tff(c_298, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_46, c_295])).
% 3.23/1.52  tff(c_301, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_92, c_298])).
% 3.23/1.52  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_301])).
% 3.23/1.52  tff(c_304, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_171])).
% 3.23/1.52  tff(c_34, plain, (![C_36, A_34]: (k1_xboole_0=C_36 | ~v1_funct_2(C_36, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.52  tff(c_373, plain, (![C_114, A_115]: (C_114='#skF_4' | ~v1_funct_2(C_114, A_115, '#skF_4') | A_115='#skF_4' | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_304, c_304, c_304, c_34])).
% 3.23/1.52  tff(c_376, plain, ('#skF_5'='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_46, c_373])).
% 3.23/1.52  tff(c_379, plain, ('#skF_5'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_376])).
% 3.23/1.52  tff(c_380, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_379])).
% 3.23/1.52  tff(c_305, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitRight, [status(thm)], [c_171])).
% 3.23/1.52  tff(c_394, plain, (k1_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_380, c_305])).
% 3.23/1.52  tff(c_400, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_48])).
% 3.23/1.52  tff(c_395, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_108])).
% 3.23/1.52  tff(c_399, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_46])).
% 3.23/1.52  tff(c_40, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.52  tff(c_465, plain, (![B_126, C_127]: (k1_relset_1('#skF_4', B_126, C_127)='#skF_4' | ~v1_funct_2(C_127, '#skF_4', B_126) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_126))))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_304, c_304, c_304, c_40])).
% 3.23/1.52  tff(c_468, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_399, c_465])).
% 3.23/1.52  tff(c_471, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_400, c_395, c_468])).
% 3.23/1.52  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_394, c_471])).
% 3.23/1.52  tff(c_474, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_379])).
% 3.23/1.52  tff(c_363, plain, (![A_111, B_112, C_113]: (r2_hidden('#skF_1'(A_111, B_112, C_113), B_112) | k2_relset_1(A_111, B_112, C_113)=B_112 | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.52  tff(c_365, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_363])).
% 3.23/1.52  tff(c_367, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_365])).
% 3.23/1.52  tff(c_368, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_93, c_367])).
% 3.23/1.52  tff(c_477, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_368])).
% 3.23/1.52  tff(c_482, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_474, c_93])).
% 3.23/1.52  tff(c_483, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_474, c_92])).
% 3.23/1.52  tff(c_486, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_46])).
% 3.23/1.52  tff(c_484, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_80])).
% 3.23/1.52  tff(c_488, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_50])).
% 3.23/1.52  tff(c_18, plain, (![A_8, B_11]: (k1_funct_1(A_8, B_11)=k1_xboole_0 | r2_hidden(B_11, k1_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.52  tff(c_314, plain, (![A_8, B_11]: (k1_funct_1(A_8, B_11)='#skF_4' | r2_hidden(B_11, k1_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_18])).
% 3.23/1.52  tff(c_579, plain, (![D_137]: (r2_hidden(k4_tarski('#skF_6'(D_137), D_137), '#skF_4') | ~r2_hidden('#skF_6'(D_137), k1_relat_1('#skF_4')) | ~r2_hidden(D_137, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_474, c_143])).
% 3.23/1.52  tff(c_28, plain, (![E_31, A_21, B_22, C_23]: (~r2_hidden(k4_tarski(E_31, '#skF_1'(A_21, B_22, C_23)), C_23) | k2_relset_1(A_21, B_22, C_23)=B_22 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.52  tff(c_622, plain, (![A_150, B_151]: (k2_relset_1(A_150, B_151, '#skF_4')=B_151 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~r2_hidden('#skF_6'('#skF_1'(A_150, B_151, '#skF_4')), k1_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_150, B_151, '#skF_4'), '#skF_4'))), inference(resolution, [status(thm)], [c_579, c_28])).
% 3.23/1.52  tff(c_625, plain, (![A_150, B_151]: (k2_relset_1(A_150, B_151, '#skF_4')=B_151 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~r2_hidden('#skF_1'(A_150, B_151, '#skF_4'), '#skF_4') | k1_funct_1('#skF_4', '#skF_6'('#skF_1'(A_150, B_151, '#skF_4')))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_314, c_622])).
% 3.23/1.52  tff(c_651, plain, (![A_164, B_165]: (k2_relset_1(A_164, B_165, '#skF_4')=B_165 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~r2_hidden('#skF_1'(A_164, B_165, '#skF_4'), '#skF_4') | k1_funct_1('#skF_4', '#skF_6'('#skF_1'(A_164, B_165, '#skF_4')))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_488, c_625])).
% 3.23/1.52  tff(c_654, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_4'), '#skF_4') | k1_funct_1('#skF_4', '#skF_6'('#skF_1'('#skF_3', '#skF_4', '#skF_4')))='#skF_4'), inference(resolution, [status(thm)], [c_486, c_651])).
% 3.23/1.52  tff(c_657, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_funct_1('#skF_4', '#skF_6'('#skF_1'('#skF_3', '#skF_4', '#skF_4')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_477, c_483, c_654])).
% 3.23/1.52  tff(c_658, plain, (k1_funct_1('#skF_4', '#skF_6'('#skF_1'('#skF_3', '#skF_4', '#skF_4')))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_482, c_657])).
% 3.23/1.52  tff(c_485, plain, (![D_40]: (k1_funct_1('#skF_4', '#skF_6'(D_40))=D_40 | ~r2_hidden(D_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_52])).
% 3.23/1.52  tff(c_662, plain, ('#skF_1'('#skF_3', '#skF_4', '#skF_4')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_658, c_485])).
% 3.23/1.52  tff(c_675, plain, ('#skF_1'('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_477, c_662])).
% 3.23/1.52  tff(c_20, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.23/1.52  tff(c_372, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_368, c_20])).
% 3.23/1.52  tff(c_476, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_372])).
% 3.23/1.52  tff(c_685, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_476])).
% 3.23/1.52  tff(c_689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_685])).
% 3.23/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.52  
% 3.23/1.52  Inference rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Ref     : 0
% 3.23/1.52  #Sup     : 122
% 3.23/1.52  #Fact    : 0
% 3.23/1.52  #Define  : 0
% 3.23/1.52  #Split   : 4
% 3.23/1.52  #Chain   : 0
% 3.23/1.52  #Close   : 0
% 3.23/1.52  
% 3.23/1.52  Ordering : KBO
% 3.23/1.52  
% 3.23/1.52  Simplification rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Subsume      : 24
% 3.23/1.52  #Demod        : 134
% 3.23/1.52  #Tautology    : 53
% 3.23/1.52  #SimpNegUnit  : 11
% 3.23/1.52  #BackRed      : 39
% 3.23/1.52  
% 3.23/1.52  #Partial instantiations: 0
% 3.23/1.52  #Strategies tried      : 1
% 3.23/1.52  
% 3.23/1.52  Timing (in seconds)
% 3.23/1.52  ----------------------
% 3.23/1.52  Preprocessing        : 0.34
% 3.23/1.52  Parsing              : 0.17
% 3.23/1.52  CNF conversion       : 0.02
% 3.23/1.52  Main loop            : 0.39
% 3.23/1.52  Inferencing          : 0.14
% 3.23/1.52  Reduction            : 0.12
% 3.23/1.52  Demodulation         : 0.08
% 3.23/1.52  BG Simplification    : 0.02
% 3.23/1.52  Subsumption          : 0.07
% 3.23/1.52  Abstraction          : 0.02
% 3.23/1.52  MUC search           : 0.00
% 3.23/1.52  Cooper               : 0.00
% 3.23/1.52  Total                : 0.79
% 3.23/1.52  Index Insertion      : 0.00
% 3.23/1.52  Index Deletion       : 0.00
% 3.23/1.52  Index Matching       : 0.00
% 3.23/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
