%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:28 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :  183 (1998 expanded)
%              Number of leaves         :   38 ( 708 expanded)
%              Depth                    :   12
%              Number of atoms          :  343 (6626 expanded)
%              Number of equality atoms :  114 (2390 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_74,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_74])).

tff(c_80,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_66,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    ! [A_13,B_36,D_51] :
      ( k1_funct_1(A_13,'#skF_5'(A_13,B_36,k9_relat_1(A_13,B_36),D_51)) = D_51
      | ~ r2_hidden(D_51,k9_relat_1(A_13,B_36))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_13,B_36,D_51] :
      ( r2_hidden('#skF_5'(A_13,B_36,k9_relat_1(A_13,B_36),D_51),B_36)
      | ~ r2_hidden(D_51,k9_relat_1(A_13,B_36))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_83,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_87,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_83])).

tff(c_2619,plain,(
    ! [B_494,A_495,C_496] :
      ( k1_xboole_0 = B_494
      | k1_relset_1(A_495,B_494,C_496) = A_495
      | ~ v1_funct_2(C_496,A_495,B_494)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(A_495,B_494))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2622,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_2619])).

tff(c_2625,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_87,c_2622])).

tff(c_2626,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2625])).

tff(c_3129,plain,(
    ! [A_577,B_578,D_579] :
      ( r2_hidden('#skF_5'(A_577,B_578,k9_relat_1(A_577,B_578),D_579),k1_relat_1(A_577))
      | ~ r2_hidden(D_579,k9_relat_1(A_577,B_578))
      | ~ v1_funct_1(A_577)
      | ~ v1_relat_1(A_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3142,plain,(
    ! [B_578,D_579] :
      ( r2_hidden('#skF_5'('#skF_9',B_578,k9_relat_1('#skF_9',B_578),D_579),'#skF_6')
      | ~ r2_hidden(D_579,k9_relat_1('#skF_9',B_578))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2626,c_3129])).

tff(c_3149,plain,(
    ! [B_580,D_581] :
      ( r2_hidden('#skF_5'('#skF_9',B_580,k9_relat_1('#skF_9',B_580),D_581),'#skF_6')
      | ~ r2_hidden(D_581,k9_relat_1('#skF_9',B_580)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_3142])).

tff(c_58,plain,(
    ! [F_71] :
      ( k1_funct_1('#skF_9',F_71) != '#skF_10'
      | ~ r2_hidden(F_71,'#skF_8')
      | ~ r2_hidden(F_71,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3304,plain,(
    ! [B_597,D_598] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_597,k9_relat_1('#skF_9',B_597),D_598)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_597,k9_relat_1('#skF_9',B_597),D_598),'#skF_8')
      | ~ r2_hidden(D_598,k9_relat_1('#skF_9',B_597)) ) ),
    inference(resolution,[status(thm)],[c_3149,c_58])).

tff(c_3308,plain,(
    ! [D_51] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_51)) != '#skF_10'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_3304])).

tff(c_3312,plain,(
    ! [D_599] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_599)) != '#skF_10'
      | ~ r2_hidden(D_599,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_3308])).

tff(c_3316,plain,(
    ! [D_51] :
      ( D_51 != '#skF_10'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3312])).

tff(c_3319,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_3316])).

tff(c_125,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128,plain,(
    ! [D_103] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_103) = k9_relat_1('#skF_9',D_103) ),
    inference(resolution,[status(thm)],[c_62,c_125])).

tff(c_60,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_130,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_60])).

tff(c_3321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3319,c_130])).

tff(c_3323,plain,(
    k1_relat_1('#skF_9') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2625])).

tff(c_3322,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2625])).

tff(c_48,plain,(
    ! [C_66,A_64] :
      ( k1_xboole_0 = C_66
      | ~ v1_funct_2(C_66,A_64,k1_xboole_0)
      | k1_xboole_0 = A_64
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4195,plain,(
    ! [C_709,A_710] :
      ( C_709 = '#skF_7'
      | ~ v1_funct_2(C_709,A_710,'#skF_7')
      | A_710 = '#skF_7'
      | ~ m1_subset_1(C_709,k1_zfmisc_1(k2_zfmisc_1(A_710,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_3322,c_3322,c_3322,c_48])).

tff(c_4198,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_62,c_4195])).

tff(c_4201,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4198])).

tff(c_4202,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4201])).

tff(c_4234,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4202,c_64])).

tff(c_4232,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4202,c_87])).

tff(c_4233,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4202,c_62])).

tff(c_54,plain,(
    ! [B_65,C_66] :
      ( k1_relset_1(k1_xboole_0,B_65,C_66) = k1_xboole_0
      | ~ v1_funct_2(C_66,k1_xboole_0,B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3329,plain,(
    ! [B_65,C_66] :
      ( k1_relset_1('#skF_7',B_65,C_66) = '#skF_7'
      | ~ v1_funct_2(C_66,'#skF_7',B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_65))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_3322,c_3322,c_3322,c_54])).

tff(c_4988,plain,(
    ! [B_779,C_780] :
      ( k1_relset_1('#skF_6',B_779,C_780) = '#skF_6'
      | ~ v1_funct_2(C_780,'#skF_6',B_779)
      | ~ m1_subset_1(C_780,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_779))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4202,c_4202,c_4202,c_4202,c_3329])).

tff(c_4991,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_4233,c_4988])).

tff(c_4994,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4234,c_4232,c_4991])).

tff(c_4996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3323,c_4994])).

tff(c_4997,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4201])).

tff(c_147,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden(k4_tarski('#skF_1'(A_112,B_113,C_114),A_112),C_114)
      | ~ r2_hidden(A_112,k9_relat_1(C_114,B_113))
      | ~ v1_relat_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_165,plain,(
    ! [A_112,B_113] :
      ( k1_funct_1('#skF_9',k4_tarski('#skF_1'(A_112,B_113,'#skF_6'),A_112)) != '#skF_10'
      | ~ r2_hidden(k4_tarski('#skF_1'(A_112,B_113,'#skF_6'),A_112),'#skF_8')
      | ~ r2_hidden(A_112,k9_relat_1('#skF_6',B_113))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_147,c_58])).

tff(c_178,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_991,plain,(
    ! [B_245,A_246,C_247] :
      ( k1_xboole_0 = B_245
      | k1_relset_1(A_246,B_245,C_247) = A_246
      | ~ v1_funct_2(C_247,A_246,B_245)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_246,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_994,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_991])).

tff(c_997,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_87,c_994])).

tff(c_998,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_997])).

tff(c_1443,plain,(
    ! [A_323,B_324,D_325] :
      ( r2_hidden('#skF_5'(A_323,B_324,k9_relat_1(A_323,B_324),D_325),k1_relat_1(A_323))
      | ~ r2_hidden(D_325,k9_relat_1(A_323,B_324))
      | ~ v1_funct_1(A_323)
      | ~ v1_relat_1(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1454,plain,(
    ! [B_324,D_325] :
      ( r2_hidden('#skF_5'('#skF_9',B_324,k9_relat_1('#skF_9',B_324),D_325),'#skF_6')
      | ~ r2_hidden(D_325,k9_relat_1('#skF_9',B_324))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_1443])).

tff(c_1460,plain,(
    ! [B_326,D_327] :
      ( r2_hidden('#skF_5'('#skF_9',B_326,k9_relat_1('#skF_9',B_326),D_327),'#skF_6')
      | ~ r2_hidden(D_327,k9_relat_1('#skF_9',B_326)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_1454])).

tff(c_1542,plain,(
    ! [B_336,D_337] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_336,k9_relat_1('#skF_9',B_336),D_337)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_336,k9_relat_1('#skF_9',B_336),D_337),'#skF_8')
      | ~ r2_hidden(D_337,k9_relat_1('#skF_9',B_336)) ) ),
    inference(resolution,[status(thm)],[c_1460,c_58])).

tff(c_1546,plain,(
    ! [D_51] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_51)) != '#skF_10'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_1542])).

tff(c_1550,plain,(
    ! [D_338] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_338)) != '#skF_10'
      | ~ r2_hidden(D_338,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_1546])).

tff(c_1554,plain,(
    ! [D_51] :
      ( D_51 != '#skF_10'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1550])).

tff(c_1557,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_1554])).

tff(c_1559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1557,c_130])).

tff(c_1560,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_997])).

tff(c_2026,plain,(
    ! [C_408,A_409] :
      ( C_408 = '#skF_7'
      | ~ v1_funct_2(C_408,A_409,'#skF_7')
      | A_409 = '#skF_7'
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_409,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1560,c_1560,c_1560,c_48])).

tff(c_2029,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_62,c_2026])).

tff(c_2032,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2029])).

tff(c_2033,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2032])).

tff(c_204,plain,(
    ! [B_130,A_131,C_132] :
      ( k1_xboole_0 = B_130
      | k1_relset_1(A_131,B_130,C_132) = A_131
      | ~ v1_funct_2(C_132,A_131,B_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_207,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_204])).

tff(c_210,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_87,c_207])).

tff(c_211,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_506,plain,(
    ! [A_178,B_179,D_180] :
      ( r2_hidden('#skF_5'(A_178,B_179,k9_relat_1(A_178,B_179),D_180),k1_relat_1(A_178))
      | ~ r2_hidden(D_180,k9_relat_1(A_178,B_179))
      | ~ v1_funct_1(A_178)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_517,plain,(
    ! [B_179,D_180] :
      ( r2_hidden('#skF_5'('#skF_9',B_179,k9_relat_1('#skF_9',B_179),D_180),'#skF_6')
      | ~ r2_hidden(D_180,k9_relat_1('#skF_9',B_179))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_506])).

tff(c_581,plain,(
    ! [B_184,D_185] :
      ( r2_hidden('#skF_5'('#skF_9',B_184,k9_relat_1('#skF_9',B_184),D_185),'#skF_6')
      | ~ r2_hidden(D_185,k9_relat_1('#skF_9',B_184)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_517])).

tff(c_600,plain,(
    ! [B_191,D_192] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_191,k9_relat_1('#skF_9',B_191),D_192)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_191,k9_relat_1('#skF_9',B_191),D_192),'#skF_8')
      | ~ r2_hidden(D_192,k9_relat_1('#skF_9',B_191)) ) ),
    inference(resolution,[status(thm)],[c_581,c_58])).

tff(c_604,plain,(
    ! [D_51] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_51)) != '#skF_10'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_600])).

tff(c_608,plain,(
    ! [D_193] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_193)) != '#skF_10'
      | ~ r2_hidden(D_193,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_604])).

tff(c_612,plain,(
    ! [D_51] :
      ( D_51 != '#skF_10'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_608])).

tff(c_615,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_612])).

tff(c_617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_615,c_130])).

tff(c_619,plain,(
    k1_relat_1('#skF_9') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_618,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_757,plain,(
    ! [C_215,A_216] :
      ( C_215 = '#skF_7'
      | ~ v1_funct_2(C_215,A_216,'#skF_7')
      | A_216 = '#skF_7'
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_216,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_618,c_618,c_618,c_48])).

tff(c_760,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_62,c_757])).

tff(c_763,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_760])).

tff(c_765,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_778,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_64])).

tff(c_776,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_87])).

tff(c_777,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_62])).

tff(c_626,plain,(
    ! [B_65,C_66] :
      ( k1_relset_1('#skF_7',B_65,C_66) = '#skF_7'
      | ~ v1_funct_2(C_66,'#skF_7',B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_65))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_618,c_618,c_618,c_54])).

tff(c_962,plain,(
    ! [B_243,C_244] :
      ( k1_relset_1('#skF_6',B_243,C_244) = '#skF_6'
      | ~ v1_funct_2(C_244,'#skF_6',B_243)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_243))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_765,c_765,c_765,c_626])).

tff(c_965,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_777,c_962])).

tff(c_968,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_776,c_965])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_968])).

tff(c_971,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [B_56,A_55] :
      ( ~ r1_tarski(B_56,A_55)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_180,plain,(
    ! [C_120,A_121,B_122] :
      ( ~ r1_tarski(C_120,k4_tarski('#skF_1'(A_121,B_122,C_120),A_121))
      | ~ r2_hidden(A_121,k9_relat_1(C_120,B_122))
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_147,c_40])).

tff(c_185,plain,(
    ! [A_121,B_122] :
      ( ~ r2_hidden(A_121,k9_relat_1(k1_xboole_0,B_122))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_180])).

tff(c_186,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_623,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_186])).

tff(c_980,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_623])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_980])).

tff(c_990,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1562,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_990])).

tff(c_2049,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2033,c_1562])).

tff(c_2056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_2049])).

tff(c_2057,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2032])).

tff(c_989,plain,(
    ! [A_121,B_122] : ~ r2_hidden(A_121,k9_relat_1(k1_xboole_0,B_122)) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1596,plain,(
    ! [A_121,B_122] : ~ r2_hidden(A_121,k9_relat_1('#skF_7',B_122)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_989])).

tff(c_2093,plain,(
    ! [A_121,B_122] : ~ r2_hidden(A_121,k9_relat_1('#skF_9',B_122)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1596])).

tff(c_2126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2093,c_130])).

tff(c_2128,plain,(
    v1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_2412,plain,(
    ! [A_471,B_472,D_473] :
      ( k1_funct_1(A_471,'#skF_5'(A_471,B_472,k9_relat_1(A_471,B_472),D_473)) = D_473
      | ~ r2_hidden(D_473,k9_relat_1(A_471,B_472))
      | ~ v1_funct_1(A_471)
      | ~ v1_relat_1(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2155,plain,(
    ! [B_429,A_430,C_431] :
      ( k1_xboole_0 = B_429
      | k1_relset_1(A_430,B_429,C_431) = A_430
      | ~ v1_funct_2(C_431,A_430,B_429)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_430,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2158,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_2155])).

tff(c_2161,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_87,c_2158])).

tff(c_2162,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2161])).

tff(c_2354,plain,(
    ! [A_451,B_452,D_453] :
      ( r2_hidden('#skF_5'(A_451,B_452,k9_relat_1(A_451,B_452),D_453),k1_relat_1(A_451))
      | ~ r2_hidden(D_453,k9_relat_1(A_451,B_452))
      | ~ v1_funct_1(A_451)
      | ~ v1_relat_1(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2363,plain,(
    ! [B_452,D_453] :
      ( r2_hidden('#skF_5'('#skF_9',B_452,k9_relat_1('#skF_9',B_452),D_453),'#skF_6')
      | ~ r2_hidden(D_453,k9_relat_1('#skF_9',B_452))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2162,c_2354])).

tff(c_2384,plain,(
    ! [B_455,D_456] :
      ( r2_hidden('#skF_5'('#skF_9',B_455,k9_relat_1('#skF_9',B_455),D_456),'#skF_6')
      | ~ r2_hidden(D_456,k9_relat_1('#skF_9',B_455)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_2363])).

tff(c_2394,plain,(
    ! [B_459,D_460] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_459,k9_relat_1('#skF_9',B_459),D_460)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_459,k9_relat_1('#skF_9',B_459),D_460),'#skF_8')
      | ~ r2_hidden(D_460,k9_relat_1('#skF_9',B_459)) ) ),
    inference(resolution,[status(thm)],[c_2384,c_58])).

tff(c_2398,plain,(
    ! [D_51] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_51)) != '#skF_10'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_2394])).

tff(c_2401,plain,(
    ! [D_51] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_51)) != '#skF_10'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_2398])).

tff(c_2426,plain,(
    ! [D_473] :
      ( D_473 != '#skF_10'
      | ~ r2_hidden(D_473,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_473,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2412,c_2401])).

tff(c_2445,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_2426])).

tff(c_2447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2445,c_130])).

tff(c_2448,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2161])).

tff(c_2575,plain,(
    ! [C_492,A_493] :
      ( C_492 = '#skF_7'
      | ~ v1_funct_2(C_492,A_493,'#skF_7')
      | A_493 = '#skF_7'
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(A_493,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2448,c_2448,c_2448,c_48])).

tff(c_2578,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_62,c_2575])).

tff(c_2581,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2578])).

tff(c_2582,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2581])).

tff(c_2136,plain,(
    ! [C_420,A_421,B_422] :
      ( ~ r1_tarski(C_420,k4_tarski('#skF_1'(A_421,B_422,C_420),A_421))
      | ~ r2_hidden(A_421,k9_relat_1(C_420,B_422))
      | ~ v1_relat_1(C_420) ) ),
    inference(resolution,[status(thm)],[c_147,c_40])).

tff(c_2141,plain,(
    ! [A_421,B_422] :
      ( ~ r2_hidden(A_421,k9_relat_1(k1_xboole_0,B_422))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_2136])).

tff(c_2142,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2141])).

tff(c_2452,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2142])).

tff(c_2590,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_2452])).

tff(c_2598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2590])).

tff(c_2599,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2581])).

tff(c_2608,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2599,c_2452])).

tff(c_2616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2608])).

tff(c_2617,plain,(
    ! [A_421,B_422] : ~ r2_hidden(A_421,k9_relat_1(k1_xboole_0,B_422)) ),
    inference(splitRight,[status(thm)],[c_2141])).

tff(c_3361,plain,(
    ! [A_421,B_422] : ~ r2_hidden(A_421,k9_relat_1('#skF_7',B_422)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_2617])).

tff(c_5011,plain,(
    ! [A_421,B_422] : ~ r2_hidden(A_421,k9_relat_1('#skF_9',B_422)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4997,c_3361])).

tff(c_5043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5011,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.18  
% 5.90/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.18  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 5.90/2.18  
% 5.90/2.18  %Foreground sorts:
% 5.90/2.18  
% 5.90/2.18  
% 5.90/2.18  %Background operators:
% 5.90/2.18  
% 5.90/2.18  
% 5.90/2.18  %Foreground operators:
% 5.90/2.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.90/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.90/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.90/2.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.90/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.90/2.18  tff('#skF_7', type, '#skF_7': $i).
% 5.90/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.90/2.18  tff('#skF_10', type, '#skF_10': $i).
% 5.90/2.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.90/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.90/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.90/2.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.90/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.90/2.18  tff('#skF_9', type, '#skF_9': $i).
% 5.90/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.90/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.90/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.90/2.18  tff('#skF_8', type, '#skF_8': $i).
% 5.90/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.90/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.90/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.90/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.90/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.90/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.90/2.18  
% 5.90/2.21  tff(f_36, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.90/2.21  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 5.90/2.21  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.90/2.21  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 5.90/2.21  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.90/2.21  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.90/2.21  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.90/2.21  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.90/2.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.90/2.21  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.90/2.21  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.90/2.21  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.90/2.21  tff(c_74, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.90/2.21  tff(c_77, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_74])).
% 5.90/2.21  tff(c_80, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_77])).
% 5.90/2.21  tff(c_66, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.90/2.21  tff(c_18, plain, (![A_13, B_36, D_51]: (k1_funct_1(A_13, '#skF_5'(A_13, B_36, k9_relat_1(A_13, B_36), D_51))=D_51 | ~r2_hidden(D_51, k9_relat_1(A_13, B_36)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.90/2.21  tff(c_20, plain, (![A_13, B_36, D_51]: (r2_hidden('#skF_5'(A_13, B_36, k9_relat_1(A_13, B_36), D_51), B_36) | ~r2_hidden(D_51, k9_relat_1(A_13, B_36)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.90/2.21  tff(c_64, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.90/2.21  tff(c_83, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.90/2.21  tff(c_87, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_83])).
% 5.90/2.21  tff(c_2619, plain, (![B_494, A_495, C_496]: (k1_xboole_0=B_494 | k1_relset_1(A_495, B_494, C_496)=A_495 | ~v1_funct_2(C_496, A_495, B_494) | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(A_495, B_494))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.90/2.21  tff(c_2622, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_2619])).
% 5.90/2.21  tff(c_2625, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_87, c_2622])).
% 5.90/2.21  tff(c_2626, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_2625])).
% 5.90/2.21  tff(c_3129, plain, (![A_577, B_578, D_579]: (r2_hidden('#skF_5'(A_577, B_578, k9_relat_1(A_577, B_578), D_579), k1_relat_1(A_577)) | ~r2_hidden(D_579, k9_relat_1(A_577, B_578)) | ~v1_funct_1(A_577) | ~v1_relat_1(A_577))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.90/2.21  tff(c_3142, plain, (![B_578, D_579]: (r2_hidden('#skF_5'('#skF_9', B_578, k9_relat_1('#skF_9', B_578), D_579), '#skF_6') | ~r2_hidden(D_579, k9_relat_1('#skF_9', B_578)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2626, c_3129])).
% 5.90/2.21  tff(c_3149, plain, (![B_580, D_581]: (r2_hidden('#skF_5'('#skF_9', B_580, k9_relat_1('#skF_9', B_580), D_581), '#skF_6') | ~r2_hidden(D_581, k9_relat_1('#skF_9', B_580)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_3142])).
% 5.90/2.21  tff(c_58, plain, (![F_71]: (k1_funct_1('#skF_9', F_71)!='#skF_10' | ~r2_hidden(F_71, '#skF_8') | ~r2_hidden(F_71, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.90/2.21  tff(c_3304, plain, (![B_597, D_598]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_597, k9_relat_1('#skF_9', B_597), D_598))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_597, k9_relat_1('#skF_9', B_597), D_598), '#skF_8') | ~r2_hidden(D_598, k9_relat_1('#skF_9', B_597)))), inference(resolution, [status(thm)], [c_3149, c_58])).
% 5.90/2.21  tff(c_3308, plain, (![D_51]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_51))!='#skF_10' | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_20, c_3304])).
% 5.90/2.21  tff(c_3312, plain, (![D_599]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_599))!='#skF_10' | ~r2_hidden(D_599, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_3308])).
% 5.90/2.21  tff(c_3316, plain, (![D_51]: (D_51!='#skF_10' | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3312])).
% 5.90/2.21  tff(c_3319, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_3316])).
% 5.90/2.21  tff(c_125, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.90/2.21  tff(c_128, plain, (![D_103]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_103)=k9_relat_1('#skF_9', D_103))), inference(resolution, [status(thm)], [c_62, c_125])).
% 5.90/2.21  tff(c_60, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.90/2.21  tff(c_130, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_60])).
% 5.90/2.21  tff(c_3321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3319, c_130])).
% 5.90/2.21  tff(c_3323, plain, (k1_relat_1('#skF_9')!='#skF_6'), inference(splitRight, [status(thm)], [c_2625])).
% 5.90/2.21  tff(c_3322, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2625])).
% 5.90/2.21  tff(c_48, plain, (![C_66, A_64]: (k1_xboole_0=C_66 | ~v1_funct_2(C_66, A_64, k1_xboole_0) | k1_xboole_0=A_64 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.90/2.21  tff(c_4195, plain, (![C_709, A_710]: (C_709='#skF_7' | ~v1_funct_2(C_709, A_710, '#skF_7') | A_710='#skF_7' | ~m1_subset_1(C_709, k1_zfmisc_1(k2_zfmisc_1(A_710, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_3322, c_3322, c_3322, c_48])).
% 5.90/2.21  tff(c_4198, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_62, c_4195])).
% 5.90/2.21  tff(c_4201, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4198])).
% 5.90/2.21  tff(c_4202, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_4201])).
% 5.90/2.21  tff(c_4234, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4202, c_64])).
% 5.90/2.21  tff(c_4232, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4202, c_87])).
% 5.90/2.21  tff(c_4233, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4202, c_62])).
% 5.90/2.21  tff(c_54, plain, (![B_65, C_66]: (k1_relset_1(k1_xboole_0, B_65, C_66)=k1_xboole_0 | ~v1_funct_2(C_66, k1_xboole_0, B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_65))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.90/2.21  tff(c_3329, plain, (![B_65, C_66]: (k1_relset_1('#skF_7', B_65, C_66)='#skF_7' | ~v1_funct_2(C_66, '#skF_7', B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_65))))), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_3322, c_3322, c_3322, c_54])).
% 5.90/2.21  tff(c_4988, plain, (![B_779, C_780]: (k1_relset_1('#skF_6', B_779, C_780)='#skF_6' | ~v1_funct_2(C_780, '#skF_6', B_779) | ~m1_subset_1(C_780, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_779))))), inference(demodulation, [status(thm), theory('equality')], [c_4202, c_4202, c_4202, c_4202, c_3329])).
% 5.90/2.21  tff(c_4991, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_4233, c_4988])).
% 5.90/2.21  tff(c_4994, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4234, c_4232, c_4991])).
% 5.90/2.21  tff(c_4996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3323, c_4994])).
% 5.90/2.21  tff(c_4997, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_4201])).
% 5.90/2.21  tff(c_147, plain, (![A_112, B_113, C_114]: (r2_hidden(k4_tarski('#skF_1'(A_112, B_113, C_114), A_112), C_114) | ~r2_hidden(A_112, k9_relat_1(C_114, B_113)) | ~v1_relat_1(C_114))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.90/2.21  tff(c_165, plain, (![A_112, B_113]: (k1_funct_1('#skF_9', k4_tarski('#skF_1'(A_112, B_113, '#skF_6'), A_112))!='#skF_10' | ~r2_hidden(k4_tarski('#skF_1'(A_112, B_113, '#skF_6'), A_112), '#skF_8') | ~r2_hidden(A_112, k9_relat_1('#skF_6', B_113)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_147, c_58])).
% 5.90/2.21  tff(c_178, plain, (~v1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_165])).
% 5.90/2.21  tff(c_991, plain, (![B_245, A_246, C_247]: (k1_xboole_0=B_245 | k1_relset_1(A_246, B_245, C_247)=A_246 | ~v1_funct_2(C_247, A_246, B_245) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_246, B_245))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.90/2.21  tff(c_994, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_991])).
% 5.90/2.21  tff(c_997, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_87, c_994])).
% 5.90/2.21  tff(c_998, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_997])).
% 5.90/2.21  tff(c_1443, plain, (![A_323, B_324, D_325]: (r2_hidden('#skF_5'(A_323, B_324, k9_relat_1(A_323, B_324), D_325), k1_relat_1(A_323)) | ~r2_hidden(D_325, k9_relat_1(A_323, B_324)) | ~v1_funct_1(A_323) | ~v1_relat_1(A_323))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.90/2.21  tff(c_1454, plain, (![B_324, D_325]: (r2_hidden('#skF_5'('#skF_9', B_324, k9_relat_1('#skF_9', B_324), D_325), '#skF_6') | ~r2_hidden(D_325, k9_relat_1('#skF_9', B_324)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_998, c_1443])).
% 5.90/2.21  tff(c_1460, plain, (![B_326, D_327]: (r2_hidden('#skF_5'('#skF_9', B_326, k9_relat_1('#skF_9', B_326), D_327), '#skF_6') | ~r2_hidden(D_327, k9_relat_1('#skF_9', B_326)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_1454])).
% 5.90/2.21  tff(c_1542, plain, (![B_336, D_337]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_336, k9_relat_1('#skF_9', B_336), D_337))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_336, k9_relat_1('#skF_9', B_336), D_337), '#skF_8') | ~r2_hidden(D_337, k9_relat_1('#skF_9', B_336)))), inference(resolution, [status(thm)], [c_1460, c_58])).
% 5.90/2.21  tff(c_1546, plain, (![D_51]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_51))!='#skF_10' | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_20, c_1542])).
% 5.90/2.21  tff(c_1550, plain, (![D_338]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_338))!='#skF_10' | ~r2_hidden(D_338, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_1546])).
% 5.90/2.21  tff(c_1554, plain, (![D_51]: (D_51!='#skF_10' | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1550])).
% 5.90/2.21  tff(c_1557, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_1554])).
% 5.90/2.21  tff(c_1559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1557, c_130])).
% 5.90/2.21  tff(c_1560, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_997])).
% 5.90/2.21  tff(c_2026, plain, (![C_408, A_409]: (C_408='#skF_7' | ~v1_funct_2(C_408, A_409, '#skF_7') | A_409='#skF_7' | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_409, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1560, c_1560, c_1560, c_48])).
% 5.90/2.21  tff(c_2029, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_62, c_2026])).
% 5.90/2.21  tff(c_2032, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2029])).
% 5.90/2.21  tff(c_2033, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_2032])).
% 5.90/2.21  tff(c_204, plain, (![B_130, A_131, C_132]: (k1_xboole_0=B_130 | k1_relset_1(A_131, B_130, C_132)=A_131 | ~v1_funct_2(C_132, A_131, B_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.90/2.21  tff(c_207, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_204])).
% 5.90/2.21  tff(c_210, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_87, c_207])).
% 5.90/2.21  tff(c_211, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_210])).
% 5.90/2.21  tff(c_506, plain, (![A_178, B_179, D_180]: (r2_hidden('#skF_5'(A_178, B_179, k9_relat_1(A_178, B_179), D_180), k1_relat_1(A_178)) | ~r2_hidden(D_180, k9_relat_1(A_178, B_179)) | ~v1_funct_1(A_178) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.90/2.21  tff(c_517, plain, (![B_179, D_180]: (r2_hidden('#skF_5'('#skF_9', B_179, k9_relat_1('#skF_9', B_179), D_180), '#skF_6') | ~r2_hidden(D_180, k9_relat_1('#skF_9', B_179)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_506])).
% 5.90/2.21  tff(c_581, plain, (![B_184, D_185]: (r2_hidden('#skF_5'('#skF_9', B_184, k9_relat_1('#skF_9', B_184), D_185), '#skF_6') | ~r2_hidden(D_185, k9_relat_1('#skF_9', B_184)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_517])).
% 5.90/2.21  tff(c_600, plain, (![B_191, D_192]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_191, k9_relat_1('#skF_9', B_191), D_192))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_191, k9_relat_1('#skF_9', B_191), D_192), '#skF_8') | ~r2_hidden(D_192, k9_relat_1('#skF_9', B_191)))), inference(resolution, [status(thm)], [c_581, c_58])).
% 5.90/2.21  tff(c_604, plain, (![D_51]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_51))!='#skF_10' | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_20, c_600])).
% 5.90/2.21  tff(c_608, plain, (![D_193]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_193))!='#skF_10' | ~r2_hidden(D_193, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_604])).
% 5.90/2.21  tff(c_612, plain, (![D_51]: (D_51!='#skF_10' | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_608])).
% 5.90/2.21  tff(c_615, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_612])).
% 5.90/2.21  tff(c_617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_615, c_130])).
% 5.90/2.21  tff(c_619, plain, (k1_relat_1('#skF_9')!='#skF_6'), inference(splitRight, [status(thm)], [c_210])).
% 5.90/2.21  tff(c_618, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_210])).
% 5.90/2.21  tff(c_757, plain, (![C_215, A_216]: (C_215='#skF_7' | ~v1_funct_2(C_215, A_216, '#skF_7') | A_216='#skF_7' | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_216, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_618, c_618, c_618, c_48])).
% 5.90/2.21  tff(c_760, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_62, c_757])).
% 5.90/2.21  tff(c_763, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_760])).
% 5.90/2.21  tff(c_765, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_763])).
% 5.90/2.21  tff(c_778, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_765, c_64])).
% 5.90/2.21  tff(c_776, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_765, c_87])).
% 5.90/2.21  tff(c_777, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_765, c_62])).
% 5.90/2.21  tff(c_626, plain, (![B_65, C_66]: (k1_relset_1('#skF_7', B_65, C_66)='#skF_7' | ~v1_funct_2(C_66, '#skF_7', B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_65))))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_618, c_618, c_618, c_54])).
% 5.90/2.21  tff(c_962, plain, (![B_243, C_244]: (k1_relset_1('#skF_6', B_243, C_244)='#skF_6' | ~v1_funct_2(C_244, '#skF_6', B_243) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_243))))), inference(demodulation, [status(thm), theory('equality')], [c_765, c_765, c_765, c_765, c_626])).
% 5.90/2.21  tff(c_965, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_777, c_962])).
% 5.90/2.21  tff(c_968, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_776, c_965])).
% 5.90/2.21  tff(c_970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_619, c_968])).
% 5.90/2.21  tff(c_971, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_763])).
% 5.90/2.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.90/2.21  tff(c_40, plain, (![B_56, A_55]: (~r1_tarski(B_56, A_55) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.90/2.21  tff(c_180, plain, (![C_120, A_121, B_122]: (~r1_tarski(C_120, k4_tarski('#skF_1'(A_121, B_122, C_120), A_121)) | ~r2_hidden(A_121, k9_relat_1(C_120, B_122)) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_147, c_40])).
% 5.90/2.21  tff(c_185, plain, (![A_121, B_122]: (~r2_hidden(A_121, k9_relat_1(k1_xboole_0, B_122)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_180])).
% 5.90/2.21  tff(c_186, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_185])).
% 5.90/2.21  tff(c_623, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_186])).
% 5.90/2.21  tff(c_980, plain, (~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_971, c_623])).
% 5.90/2.21  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_980])).
% 5.90/2.21  tff(c_990, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_185])).
% 5.90/2.21  tff(c_1562, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_990])).
% 5.90/2.21  tff(c_2049, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2033, c_1562])).
% 5.90/2.21  tff(c_2056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_2049])).
% 5.90/2.21  tff(c_2057, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_2032])).
% 5.90/2.21  tff(c_989, plain, (![A_121, B_122]: (~r2_hidden(A_121, k9_relat_1(k1_xboole_0, B_122)))), inference(splitRight, [status(thm)], [c_185])).
% 5.90/2.21  tff(c_1596, plain, (![A_121, B_122]: (~r2_hidden(A_121, k9_relat_1('#skF_7', B_122)))), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_989])).
% 5.90/2.21  tff(c_2093, plain, (![A_121, B_122]: (~r2_hidden(A_121, k9_relat_1('#skF_9', B_122)))), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_1596])).
% 5.90/2.21  tff(c_2126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2093, c_130])).
% 5.90/2.21  tff(c_2128, plain, (v1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_165])).
% 5.90/2.21  tff(c_2412, plain, (![A_471, B_472, D_473]: (k1_funct_1(A_471, '#skF_5'(A_471, B_472, k9_relat_1(A_471, B_472), D_473))=D_473 | ~r2_hidden(D_473, k9_relat_1(A_471, B_472)) | ~v1_funct_1(A_471) | ~v1_relat_1(A_471))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.90/2.21  tff(c_2155, plain, (![B_429, A_430, C_431]: (k1_xboole_0=B_429 | k1_relset_1(A_430, B_429, C_431)=A_430 | ~v1_funct_2(C_431, A_430, B_429) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_430, B_429))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.90/2.21  tff(c_2158, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_2155])).
% 5.90/2.21  tff(c_2161, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_87, c_2158])).
% 5.90/2.21  tff(c_2162, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_2161])).
% 5.90/2.21  tff(c_2354, plain, (![A_451, B_452, D_453]: (r2_hidden('#skF_5'(A_451, B_452, k9_relat_1(A_451, B_452), D_453), k1_relat_1(A_451)) | ~r2_hidden(D_453, k9_relat_1(A_451, B_452)) | ~v1_funct_1(A_451) | ~v1_relat_1(A_451))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.90/2.21  tff(c_2363, plain, (![B_452, D_453]: (r2_hidden('#skF_5'('#skF_9', B_452, k9_relat_1('#skF_9', B_452), D_453), '#skF_6') | ~r2_hidden(D_453, k9_relat_1('#skF_9', B_452)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2162, c_2354])).
% 5.90/2.21  tff(c_2384, plain, (![B_455, D_456]: (r2_hidden('#skF_5'('#skF_9', B_455, k9_relat_1('#skF_9', B_455), D_456), '#skF_6') | ~r2_hidden(D_456, k9_relat_1('#skF_9', B_455)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_2363])).
% 5.90/2.21  tff(c_2394, plain, (![B_459, D_460]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_459, k9_relat_1('#skF_9', B_459), D_460))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_459, k9_relat_1('#skF_9', B_459), D_460), '#skF_8') | ~r2_hidden(D_460, k9_relat_1('#skF_9', B_459)))), inference(resolution, [status(thm)], [c_2384, c_58])).
% 5.90/2.21  tff(c_2398, plain, (![D_51]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_51))!='#skF_10' | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_20, c_2394])).
% 5.90/2.21  tff(c_2401, plain, (![D_51]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_51))!='#skF_10' | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_2398])).
% 5.90/2.21  tff(c_2426, plain, (![D_473]: (D_473!='#skF_10' | ~r2_hidden(D_473, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_473, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2412, c_2401])).
% 5.90/2.21  tff(c_2445, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_2426])).
% 5.90/2.21  tff(c_2447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2445, c_130])).
% 5.90/2.21  tff(c_2448, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2161])).
% 5.90/2.21  tff(c_2575, plain, (![C_492, A_493]: (C_492='#skF_7' | ~v1_funct_2(C_492, A_493, '#skF_7') | A_493='#skF_7' | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(A_493, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2448, c_2448, c_2448, c_48])).
% 5.90/2.21  tff(c_2578, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_62, c_2575])).
% 5.90/2.21  tff(c_2581, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2578])).
% 5.90/2.21  tff(c_2582, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_2581])).
% 5.90/2.21  tff(c_2136, plain, (![C_420, A_421, B_422]: (~r1_tarski(C_420, k4_tarski('#skF_1'(A_421, B_422, C_420), A_421)) | ~r2_hidden(A_421, k9_relat_1(C_420, B_422)) | ~v1_relat_1(C_420))), inference(resolution, [status(thm)], [c_147, c_40])).
% 5.90/2.21  tff(c_2141, plain, (![A_421, B_422]: (~r2_hidden(A_421, k9_relat_1(k1_xboole_0, B_422)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_2136])).
% 5.90/2.21  tff(c_2142, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2141])).
% 5.90/2.21  tff(c_2452, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2142])).
% 5.90/2.21  tff(c_2590, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_2452])).
% 5.90/2.21  tff(c_2598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2590])).
% 5.90/2.21  tff(c_2599, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_2581])).
% 5.90/2.21  tff(c_2608, plain, (~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2599, c_2452])).
% 5.90/2.21  tff(c_2616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2608])).
% 5.90/2.21  tff(c_2617, plain, (![A_421, B_422]: (~r2_hidden(A_421, k9_relat_1(k1_xboole_0, B_422)))), inference(splitRight, [status(thm)], [c_2141])).
% 5.90/2.21  tff(c_3361, plain, (![A_421, B_422]: (~r2_hidden(A_421, k9_relat_1('#skF_7', B_422)))), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_2617])).
% 5.90/2.21  tff(c_5011, plain, (![A_421, B_422]: (~r2_hidden(A_421, k9_relat_1('#skF_9', B_422)))), inference(demodulation, [status(thm), theory('equality')], [c_4997, c_3361])).
% 5.90/2.21  tff(c_5043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5011, c_130])).
% 5.90/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.21  
% 5.90/2.21  Inference rules
% 5.90/2.21  ----------------------
% 5.90/2.21  #Ref     : 0
% 5.90/2.21  #Sup     : 956
% 5.90/2.21  #Fact    : 0
% 5.90/2.21  #Define  : 0
% 5.90/2.21  #Split   : 23
% 5.90/2.21  #Chain   : 0
% 5.90/2.21  #Close   : 0
% 5.90/2.21  
% 5.90/2.21  Ordering : KBO
% 5.90/2.21  
% 5.90/2.21  Simplification rules
% 5.90/2.21  ----------------------
% 5.90/2.21  #Subsume      : 208
% 5.90/2.21  #Demod        : 619
% 5.90/2.21  #Tautology    : 102
% 5.90/2.21  #SimpNegUnit  : 11
% 5.90/2.21  #BackRed      : 267
% 5.90/2.21  
% 5.90/2.21  #Partial instantiations: 0
% 5.90/2.21  #Strategies tried      : 1
% 5.90/2.21  
% 5.90/2.21  Timing (in seconds)
% 5.90/2.21  ----------------------
% 5.90/2.21  Preprocessing        : 0.36
% 5.90/2.21  Parsing              : 0.18
% 5.90/2.21  CNF conversion       : 0.03
% 5.90/2.21  Main loop            : 1.05
% 5.90/2.21  Inferencing          : 0.38
% 5.90/2.21  Reduction            : 0.27
% 5.90/2.21  Demodulation         : 0.20
% 5.90/2.21  BG Simplification    : 0.05
% 5.90/2.21  Subsumption          : 0.26
% 5.90/2.21  Abstraction          : 0.05
% 5.90/2.21  MUC search           : 0.00
% 5.90/2.21  Cooper               : 0.00
% 5.90/2.21  Total                : 1.47
% 5.90/2.21  Index Insertion      : 0.00
% 5.90/2.21  Index Deletion       : 0.00
% 5.90/2.21  Index Matching       : 0.00
% 5.90/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
