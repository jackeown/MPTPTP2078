%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:43 EST 2020

% Result     : Theorem 12.69s
% Output     : CNFRefutation 12.88s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 256 expanded)
%              Number of leaves         :   35 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  176 ( 602 expanded)
%              Number of equality atoms :   67 ( 200 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_136,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_123,axiom,(
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

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36179,plain,(
    ! [A_17723,B_17724] :
      ( r2_hidden('#skF_2'(A_17723,B_17724),A_17723)
      | r1_tarski(A_17723,B_17724) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36187,plain,(
    ! [A_17723] : r1_tarski(A_17723,A_17723) ),
    inference(resolution,[status(thm)],[c_36179,c_8])).

tff(c_37046,plain,(
    ! [C_18549,A_18550,B_18551] :
      ( m1_subset_1(C_18549,k1_zfmisc_1(k2_zfmisc_1(A_18550,B_18551)))
      | ~ r1_tarski(k2_relat_1(C_18549),B_18551)
      | ~ r1_tarski(k1_relat_1(C_18549),A_18550)
      | ~ v1_relat_1(C_18549) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ! [A_38,B_39] : v1_relat_1('#skF_3'(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_220,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_228,plain,(
    ! [A_74] : r1_tarski(A_74,A_74) ),
    inference(resolution,[status(thm)],[c_220,c_8])).

tff(c_705,plain,(
    ! [C_135,A_136,B_137] :
      ( m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ r1_tarski(k2_relat_1(C_135),B_137)
      | ~ r1_tarski(k1_relat_1(C_135),A_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4150,plain,(
    ! [A_3405,B_3406,C_3407] :
      ( k1_relset_1(A_3405,B_3406,C_3407) = k1_relat_1(C_3407)
      | ~ r1_tarski(k2_relat_1(C_3407),B_3406)
      | ~ r1_tarski(k1_relat_1(C_3407),A_3405)
      | ~ v1_relat_1(C_3407) ) ),
    inference(resolution,[status(thm)],[c_705,c_44])).

tff(c_13803,plain,(
    ! [A_3715,C_3716] :
      ( k1_relset_1(A_3715,k2_relat_1(C_3716),C_3716) = k1_relat_1(C_3716)
      | ~ r1_tarski(k1_relat_1(C_3716),A_3715)
      | ~ v1_relat_1(C_3716) ) ),
    inference(resolution,[status(thm)],[c_228,c_4150])).

tff(c_13853,plain,(
    ! [C_3716] :
      ( k1_relset_1(k1_relat_1(C_3716),k2_relat_1(C_3716),C_3716) = k1_relat_1(C_3716)
      | ~ v1_relat_1(C_3716) ) ),
    inference(resolution,[status(thm)],[c_228,c_13803])).

tff(c_177,plain,(
    ! [A_65] :
      ( k2_relat_1(A_65) != k1_xboole_0
      | k1_xboole_0 = A_65
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_185,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_177])).

tff(c_187,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_46,plain,(
    ! [C_34,A_32,B_33] :
      ( m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ r1_tarski(k2_relat_1(C_34),B_33)
      | ~ r1_tarski(k1_relat_1(C_34),A_32)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1155,plain,(
    ! [B_1052,C_1053,A_1054] :
      ( k1_xboole_0 = B_1052
      | v1_funct_2(C_1053,A_1054,B_1052)
      | k1_relset_1(A_1054,B_1052,C_1053) != A_1054
      | ~ m1_subset_1(C_1053,k1_zfmisc_1(k2_zfmisc_1(A_1054,B_1052))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5821,plain,(
    ! [B_3478,C_3479,A_3480] :
      ( k1_xboole_0 = B_3478
      | v1_funct_2(C_3479,A_3480,B_3478)
      | k1_relset_1(A_3480,B_3478,C_3479) != A_3480
      | ~ r1_tarski(k2_relat_1(C_3479),B_3478)
      | ~ r1_tarski(k1_relat_1(C_3479),A_3480)
      | ~ v1_relat_1(C_3479) ) ),
    inference(resolution,[status(thm)],[c_46,c_1155])).

tff(c_34975,plain,(
    ! [C_17590,A_17591] :
      ( k2_relat_1(C_17590) = k1_xboole_0
      | v1_funct_2(C_17590,A_17591,k2_relat_1(C_17590))
      | k1_relset_1(A_17591,k2_relat_1(C_17590),C_17590) != A_17591
      | ~ r1_tarski(k1_relat_1(C_17590),A_17591)
      | ~ v1_relat_1(C_17590) ) ),
    inference(resolution,[status(thm)],[c_228,c_5821])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72])).

tff(c_116,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_34984,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34975,c_116])).

tff(c_35038,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_228,c_34984])).

tff(c_35039,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_35038])).

tff(c_35070,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13853,c_35039])).

tff(c_35074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_35070])).

tff(c_35075,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_35091,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35075,c_35075,c_34])).

tff(c_168,plain,(
    ! [A_64] :
      ( k1_relat_1(A_64) != k1_xboole_0
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_176,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_168])).

tff(c_186,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_35077,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35075,c_186])).

tff(c_35109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35091,c_35077])).

tff(c_35110,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_141,plain,(
    ! [A_59] :
      ( k7_relat_1(A_59,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_148,plain,(
    ! [A_38,B_39] : k7_relat_1('#skF_3'(A_38,B_39),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_141])).

tff(c_35114,plain,(
    ! [A_38,B_39] : k7_relat_1('#skF_3'(A_38,B_39),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35110,c_35110,c_148])).

tff(c_18,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35122,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_4',B_11) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35110,c_35110,c_18])).

tff(c_35242,plain,(
    ! [A_17610,B_17611] : m1_subset_1('#skF_3'(A_17610,B_17611),k1_zfmisc_1(k2_zfmisc_1(A_17610,B_17611))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_35248,plain,(
    ! [B_11] : m1_subset_1('#skF_3'('#skF_4',B_11),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35122,c_35242])).

tff(c_70,plain,(
    ! [A_38,B_39] : m1_subset_1('#skF_3'(A_38,B_39),k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_35611,plain,(
    ! [A_17660,B_17661,C_17662] :
      ( k1_relset_1(A_17660,B_17661,C_17662) = k1_relat_1(C_17662)
      | ~ m1_subset_1(C_17662,k1_zfmisc_1(k2_zfmisc_1(A_17660,B_17661))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_35635,plain,(
    ! [A_38,B_39] : k1_relset_1(A_38,B_39,'#skF_3'(A_38,B_39)) = k1_relat_1('#skF_3'(A_38,B_39)) ),
    inference(resolution,[status(thm)],[c_70,c_35611])).

tff(c_60,plain,(
    ! [A_38,B_39] : v1_funct_2('#skF_3'(A_38,B_39),A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56,plain,(
    ! [B_36,C_37] :
      ( k1_relset_1(k1_xboole_0,B_36,C_37) = k1_xboole_0
      | ~ v1_funct_2(C_37,k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_81,plain,(
    ! [B_36,C_37] :
      ( k1_relset_1(k1_xboole_0,B_36,C_37) = k1_xboole_0
      | ~ v1_funct_2(C_37,k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_56])).

tff(c_35882,plain,(
    ! [B_17690,C_17691] :
      ( k1_relset_1('#skF_4',B_17690,C_17691) = '#skF_4'
      | ~ v1_funct_2(C_17691,'#skF_4',B_17690)
      | ~ m1_subset_1(C_17691,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35110,c_35110,c_35110,c_35110,c_81])).

tff(c_35888,plain,(
    ! [B_39] :
      ( k1_relset_1('#skF_4',B_39,'#skF_3'('#skF_4',B_39)) = '#skF_4'
      | ~ m1_subset_1('#skF_3'('#skF_4',B_39),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_60,c_35882])).

tff(c_35896,plain,(
    ! [B_17692] : k1_relat_1('#skF_3'('#skF_4',B_17692)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35248,c_35635,c_35888])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35268,plain,(
    ! [A_17615,B_17616] :
      ( ~ r2_hidden('#skF_2'(A_17615,B_17616),B_17616)
      | r1_tarski(A_17615,B_17616) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35273,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_35268])).

tff(c_35427,plain,(
    ! [B_17645,A_17646] :
      ( k7_relat_1(B_17645,A_17646) = B_17645
      | ~ r1_tarski(k1_relat_1(B_17645),A_17646)
      | ~ v1_relat_1(B_17645) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_35439,plain,(
    ! [B_17645] :
      ( k7_relat_1(B_17645,k1_relat_1(B_17645)) = B_17645
      | ~ v1_relat_1(B_17645) ) ),
    inference(resolution,[status(thm)],[c_35273,c_35427])).

tff(c_35916,plain,(
    ! [B_17692] :
      ( k7_relat_1('#skF_3'('#skF_4',B_17692),'#skF_4') = '#skF_3'('#skF_4',B_17692)
      | ~ v1_relat_1('#skF_3'('#skF_4',B_17692)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35896,c_35439])).

tff(c_35956,plain,(
    ! [B_17693] : '#skF_3'('#skF_4',B_17693) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_35114,c_35916])).

tff(c_36006,plain,(
    ! [B_17693] : v1_funct_2('#skF_4','#skF_4',B_17693) ),
    inference(superposition,[status(thm),theory(equality)],[c_35956,c_60])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_35124,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35110,c_35110,c_32])).

tff(c_35111,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_35132,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35110,c_35111])).

tff(c_35133,plain,(
    ~ v1_funct_2('#skF_4','#skF_4',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35132,c_116])).

tff(c_35193,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35124,c_35133])).

tff(c_36095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36006,c_35193])).

tff(c_36096,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_37057,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_37046,c_36096])).

tff(c_37070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_36187,c_36187,c_37057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:25:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.69/5.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.69/5.36  
% 12.69/5.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.69/5.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 12.69/5.36  
% 12.69/5.36  %Foreground sorts:
% 12.69/5.36  
% 12.69/5.36  
% 12.69/5.36  %Background operators:
% 12.69/5.36  
% 12.69/5.36  
% 12.69/5.36  %Foreground operators:
% 12.69/5.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.69/5.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.69/5.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.69/5.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.69/5.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.69/5.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.69/5.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.69/5.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.69/5.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.69/5.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.69/5.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.69/5.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.69/5.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.69/5.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.69/5.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.69/5.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.69/5.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.69/5.36  tff('#skF_4', type, '#skF_4': $i).
% 12.69/5.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.69/5.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.69/5.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.69/5.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.69/5.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.69/5.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.69/5.36  
% 12.88/5.38  tff(f_147, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.88/5.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.88/5.38  tff(f_105, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 12.88/5.38  tff(f_136, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 12.88/5.38  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.88/5.38  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 12.88/5.38  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.88/5.38  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 12.88/5.38  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 12.88/5.38  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.88/5.38  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 12.88/5.38  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.88/5.38  tff(c_36179, plain, (![A_17723, B_17724]: (r2_hidden('#skF_2'(A_17723, B_17724), A_17723) | r1_tarski(A_17723, B_17724))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.88/5.38  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.88/5.38  tff(c_36187, plain, (![A_17723]: (r1_tarski(A_17723, A_17723))), inference(resolution, [status(thm)], [c_36179, c_8])).
% 12.88/5.38  tff(c_37046, plain, (![C_18549, A_18550, B_18551]: (m1_subset_1(C_18549, k1_zfmisc_1(k2_zfmisc_1(A_18550, B_18551))) | ~r1_tarski(k2_relat_1(C_18549), B_18551) | ~r1_tarski(k1_relat_1(C_18549), A_18550) | ~v1_relat_1(C_18549))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.88/5.38  tff(c_68, plain, (![A_38, B_39]: (v1_relat_1('#skF_3'(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.88/5.38  tff(c_220, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), A_74) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.88/5.38  tff(c_228, plain, (![A_74]: (r1_tarski(A_74, A_74))), inference(resolution, [status(thm)], [c_220, c_8])).
% 12.88/5.38  tff(c_705, plain, (![C_135, A_136, B_137]: (m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~r1_tarski(k2_relat_1(C_135), B_137) | ~r1_tarski(k1_relat_1(C_135), A_136) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.88/5.38  tff(c_44, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.88/5.38  tff(c_4150, plain, (![A_3405, B_3406, C_3407]: (k1_relset_1(A_3405, B_3406, C_3407)=k1_relat_1(C_3407) | ~r1_tarski(k2_relat_1(C_3407), B_3406) | ~r1_tarski(k1_relat_1(C_3407), A_3405) | ~v1_relat_1(C_3407))), inference(resolution, [status(thm)], [c_705, c_44])).
% 12.88/5.38  tff(c_13803, plain, (![A_3715, C_3716]: (k1_relset_1(A_3715, k2_relat_1(C_3716), C_3716)=k1_relat_1(C_3716) | ~r1_tarski(k1_relat_1(C_3716), A_3715) | ~v1_relat_1(C_3716))), inference(resolution, [status(thm)], [c_228, c_4150])).
% 12.88/5.38  tff(c_13853, plain, (![C_3716]: (k1_relset_1(k1_relat_1(C_3716), k2_relat_1(C_3716), C_3716)=k1_relat_1(C_3716) | ~v1_relat_1(C_3716))), inference(resolution, [status(thm)], [c_228, c_13803])).
% 12.88/5.38  tff(c_177, plain, (![A_65]: (k2_relat_1(A_65)!=k1_xboole_0 | k1_xboole_0=A_65 | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.88/5.38  tff(c_185, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_76, c_177])).
% 12.88/5.38  tff(c_187, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_185])).
% 12.88/5.38  tff(c_46, plain, (![C_34, A_32, B_33]: (m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~r1_tarski(k2_relat_1(C_34), B_33) | ~r1_tarski(k1_relat_1(C_34), A_32) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.88/5.38  tff(c_1155, plain, (![B_1052, C_1053, A_1054]: (k1_xboole_0=B_1052 | v1_funct_2(C_1053, A_1054, B_1052) | k1_relset_1(A_1054, B_1052, C_1053)!=A_1054 | ~m1_subset_1(C_1053, k1_zfmisc_1(k2_zfmisc_1(A_1054, B_1052))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.88/5.38  tff(c_5821, plain, (![B_3478, C_3479, A_3480]: (k1_xboole_0=B_3478 | v1_funct_2(C_3479, A_3480, B_3478) | k1_relset_1(A_3480, B_3478, C_3479)!=A_3480 | ~r1_tarski(k2_relat_1(C_3479), B_3478) | ~r1_tarski(k1_relat_1(C_3479), A_3480) | ~v1_relat_1(C_3479))), inference(resolution, [status(thm)], [c_46, c_1155])).
% 12.88/5.38  tff(c_34975, plain, (![C_17590, A_17591]: (k2_relat_1(C_17590)=k1_xboole_0 | v1_funct_2(C_17590, A_17591, k2_relat_1(C_17590)) | k1_relset_1(A_17591, k2_relat_1(C_17590), C_17590)!=A_17591 | ~r1_tarski(k1_relat_1(C_17590), A_17591) | ~v1_relat_1(C_17590))), inference(resolution, [status(thm)], [c_228, c_5821])).
% 12.88/5.38  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.88/5.38  tff(c_72, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.88/5.38  tff(c_78, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72])).
% 12.88/5.38  tff(c_116, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_78])).
% 12.88/5.38  tff(c_34984, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34975, c_116])).
% 12.88/5.38  tff(c_35038, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_228, c_34984])).
% 12.88/5.38  tff(c_35039, plain, (k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_187, c_35038])).
% 12.88/5.38  tff(c_35070, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13853, c_35039])).
% 12.88/5.38  tff(c_35074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_35070])).
% 12.88/5.38  tff(c_35075, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_185])).
% 12.88/5.38  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.88/5.38  tff(c_35091, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35075, c_35075, c_34])).
% 12.88/5.38  tff(c_168, plain, (![A_64]: (k1_relat_1(A_64)!=k1_xboole_0 | k1_xboole_0=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.88/5.38  tff(c_176, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_76, c_168])).
% 12.88/5.38  tff(c_186, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_176])).
% 12.88/5.38  tff(c_35077, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35075, c_186])).
% 12.88/5.38  tff(c_35109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35091, c_35077])).
% 12.88/5.38  tff(c_35110, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_176])).
% 12.88/5.38  tff(c_141, plain, (![A_59]: (k7_relat_1(A_59, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.88/5.38  tff(c_148, plain, (![A_38, B_39]: (k7_relat_1('#skF_3'(A_38, B_39), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_141])).
% 12.88/5.38  tff(c_35114, plain, (![A_38, B_39]: (k7_relat_1('#skF_3'(A_38, B_39), '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35110, c_35110, c_148])).
% 12.88/5.38  tff(c_18, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.88/5.38  tff(c_35122, plain, (![B_11]: (k2_zfmisc_1('#skF_4', B_11)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35110, c_35110, c_18])).
% 12.88/5.38  tff(c_35242, plain, (![A_17610, B_17611]: (m1_subset_1('#skF_3'(A_17610, B_17611), k1_zfmisc_1(k2_zfmisc_1(A_17610, B_17611))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.88/5.38  tff(c_35248, plain, (![B_11]: (m1_subset_1('#skF_3'('#skF_4', B_11), k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_35122, c_35242])).
% 12.88/5.38  tff(c_70, plain, (![A_38, B_39]: (m1_subset_1('#skF_3'(A_38, B_39), k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.88/5.38  tff(c_35611, plain, (![A_17660, B_17661, C_17662]: (k1_relset_1(A_17660, B_17661, C_17662)=k1_relat_1(C_17662) | ~m1_subset_1(C_17662, k1_zfmisc_1(k2_zfmisc_1(A_17660, B_17661))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.88/5.38  tff(c_35635, plain, (![A_38, B_39]: (k1_relset_1(A_38, B_39, '#skF_3'(A_38, B_39))=k1_relat_1('#skF_3'(A_38, B_39)))), inference(resolution, [status(thm)], [c_70, c_35611])).
% 12.88/5.38  tff(c_60, plain, (![A_38, B_39]: (v1_funct_2('#skF_3'(A_38, B_39), A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.88/5.38  tff(c_56, plain, (![B_36, C_37]: (k1_relset_1(k1_xboole_0, B_36, C_37)=k1_xboole_0 | ~v1_funct_2(C_37, k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.88/5.38  tff(c_81, plain, (![B_36, C_37]: (k1_relset_1(k1_xboole_0, B_36, C_37)=k1_xboole_0 | ~v1_funct_2(C_37, k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_56])).
% 12.88/5.38  tff(c_35882, plain, (![B_17690, C_17691]: (k1_relset_1('#skF_4', B_17690, C_17691)='#skF_4' | ~v1_funct_2(C_17691, '#skF_4', B_17690) | ~m1_subset_1(C_17691, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_35110, c_35110, c_35110, c_35110, c_81])).
% 12.88/5.38  tff(c_35888, plain, (![B_39]: (k1_relset_1('#skF_4', B_39, '#skF_3'('#skF_4', B_39))='#skF_4' | ~m1_subset_1('#skF_3'('#skF_4', B_39), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_60, c_35882])).
% 12.88/5.38  tff(c_35896, plain, (![B_17692]: (k1_relat_1('#skF_3'('#skF_4', B_17692))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35248, c_35635, c_35888])).
% 12.88/5.38  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.88/5.38  tff(c_35268, plain, (![A_17615, B_17616]: (~r2_hidden('#skF_2'(A_17615, B_17616), B_17616) | r1_tarski(A_17615, B_17616))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.88/5.38  tff(c_35273, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_35268])).
% 12.88/5.38  tff(c_35427, plain, (![B_17645, A_17646]: (k7_relat_1(B_17645, A_17646)=B_17645 | ~r1_tarski(k1_relat_1(B_17645), A_17646) | ~v1_relat_1(B_17645))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.88/5.38  tff(c_35439, plain, (![B_17645]: (k7_relat_1(B_17645, k1_relat_1(B_17645))=B_17645 | ~v1_relat_1(B_17645))), inference(resolution, [status(thm)], [c_35273, c_35427])).
% 12.88/5.38  tff(c_35916, plain, (![B_17692]: (k7_relat_1('#skF_3'('#skF_4', B_17692), '#skF_4')='#skF_3'('#skF_4', B_17692) | ~v1_relat_1('#skF_3'('#skF_4', B_17692)))), inference(superposition, [status(thm), theory('equality')], [c_35896, c_35439])).
% 12.88/5.38  tff(c_35956, plain, (![B_17693]: ('#skF_3'('#skF_4', B_17693)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_35114, c_35916])).
% 12.88/5.38  tff(c_36006, plain, (![B_17693]: (v1_funct_2('#skF_4', '#skF_4', B_17693))), inference(superposition, [status(thm), theory('equality')], [c_35956, c_60])).
% 12.88/5.38  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.88/5.38  tff(c_35124, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35110, c_35110, c_32])).
% 12.88/5.38  tff(c_35111, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_176])).
% 12.88/5.38  tff(c_35132, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35110, c_35111])).
% 12.88/5.38  tff(c_35133, plain, (~v1_funct_2('#skF_4', '#skF_4', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35132, c_116])).
% 12.88/5.38  tff(c_35193, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35124, c_35133])).
% 12.88/5.38  tff(c_36095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36006, c_35193])).
% 12.88/5.38  tff(c_36096, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(splitRight, [status(thm)], [c_78])).
% 12.88/5.38  tff(c_37057, plain, (~r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_37046, c_36096])).
% 12.88/5.38  tff(c_37070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_36187, c_36187, c_37057])).
% 12.88/5.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.88/5.38  
% 12.88/5.38  Inference rules
% 12.88/5.38  ----------------------
% 12.88/5.38  #Ref     : 0
% 12.88/5.38  #Sup     : 8625
% 12.88/5.38  #Fact    : 4
% 12.88/5.38  #Define  : 0
% 12.88/5.38  #Split   : 27
% 12.88/5.38  #Chain   : 0
% 12.88/5.38  #Close   : 0
% 12.88/5.38  
% 12.88/5.38  Ordering : KBO
% 12.88/5.38  
% 12.88/5.38  Simplification rules
% 12.88/5.38  ----------------------
% 12.88/5.38  #Subsume      : 1627
% 12.88/5.38  #Demod        : 10431
% 12.88/5.38  #Tautology    : 5108
% 12.88/5.38  #SimpNegUnit  : 108
% 12.88/5.38  #BackRed      : 132
% 12.88/5.38  
% 12.88/5.38  #Partial instantiations: 1019
% 12.88/5.38  #Strategies tried      : 1
% 12.88/5.38  
% 12.88/5.38  Timing (in seconds)
% 12.88/5.38  ----------------------
% 12.88/5.38  Preprocessing        : 0.37
% 12.88/5.38  Parsing              : 0.20
% 12.88/5.38  CNF conversion       : 0.03
% 12.88/5.38  Main loop            : 4.17
% 12.88/5.38  Inferencing          : 1.11
% 12.88/5.38  Reduction            : 1.43
% 12.88/5.38  Demodulation         : 1.08
% 12.88/5.38  BG Simplification    : 0.11
% 12.88/5.38  Subsumption          : 1.27
% 12.88/5.38  Abstraction          : 0.17
% 12.88/5.38  MUC search           : 0.00
% 12.88/5.38  Cooper               : 0.00
% 12.88/5.38  Total                : 4.58
% 12.88/5.38  Index Insertion      : 0.00
% 12.88/5.38  Index Deletion       : 0.00
% 12.88/5.38  Index Matching       : 0.00
% 12.88/5.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
