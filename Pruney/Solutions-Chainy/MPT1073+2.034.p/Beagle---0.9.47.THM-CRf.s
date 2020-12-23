%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:02 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 188 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 445 expanded)
%              Number of equality atoms :   33 ( 121 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_88,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_92,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_111,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1(k2_relset_1(A_59,B_60,C_61),k1_zfmisc_1(B_60))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_111])).

tff(c_134,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_128])).

tff(c_6,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_3,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_134,c_6])).

tff(c_138,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_46,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_94,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_46])).

tff(c_59,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_79,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_83,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_79])).

tff(c_335,plain,(
    ! [B_100,A_101,C_102] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_101,B_100,C_102) = A_101
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_350,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_335])).

tff(c_356,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_350])).

tff(c_357,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_16,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_1'(A_53,B_54,C_55),B_54)
      | ~ r2_hidden(A_53,k9_relat_1(C_55,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_144,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1('#skF_1'(A_65,B_66,C_67),B_66)
      | ~ r2_hidden(A_65,k9_relat_1(C_67,B_66))
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_149,plain,(
    ! [A_65,A_12] :
      ( m1_subset_1('#skF_1'(A_65,k1_relat_1(A_12),A_12),k1_relat_1(A_12))
      | ~ r2_hidden(A_65,k2_relat_1(A_12))
      | ~ v1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_144])).

tff(c_365,plain,(
    ! [A_65] :
      ( m1_subset_1('#skF_1'(A_65,k1_relat_1('#skF_5'),'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_65,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_149])).

tff(c_404,plain,(
    ! [A_103] :
      ( m1_subset_1('#skF_1'(A_103,'#skF_3','#skF_5'),'#skF_3')
      | ~ r2_hidden(A_103,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_357,c_365])).

tff(c_423,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_404])).

tff(c_44,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) != '#skF_2'
      | ~ m1_subset_1(E_32,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_427,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_423,c_44])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_374,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_16])).

tff(c_386,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_374])).

tff(c_167,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden(k4_tarski('#skF_1'(A_77,B_78,C_79),A_77),C_79)
      | ~ r2_hidden(A_77,k9_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( k1_funct_1(C_15,A_13) = B_14
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_185,plain,(
    ! [C_79,A_77,B_78] :
      ( k1_funct_1(C_79,'#skF_1'(A_77,B_78,C_79)) = A_77
      | ~ v1_funct_1(C_79)
      | ~ r2_hidden(A_77,k9_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_167,c_20])).

tff(c_394,plain,(
    ! [A_77] :
      ( k1_funct_1('#skF_5','#skF_1'(A_77,'#skF_3','#skF_5')) = A_77
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_77,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_185])).

tff(c_480,plain,(
    ! [A_111] :
      ( k1_funct_1('#skF_5','#skF_1'(A_111,'#skF_3','#skF_5')) = A_111
      | ~ r2_hidden(A_111,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_52,c_394])).

tff(c_495,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_94,c_480])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_495])).

tff(c_503,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_510,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_2])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_510])).

tff(c_513,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_513,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.83  
% 3.28/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.84  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.58/1.84  
% 3.58/1.84  %Foreground sorts:
% 3.58/1.84  
% 3.58/1.84  
% 3.58/1.84  %Background operators:
% 3.58/1.84  
% 3.58/1.84  
% 3.58/1.84  %Foreground operators:
% 3.58/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.58/1.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.58/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.58/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.58/1.84  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.84  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.58/1.84  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.58/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.58/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.84  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.58/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.84  
% 3.58/1.86  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.58/1.86  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.58/1.86  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.58/1.86  tff(f_37, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.58/1.86  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.58/1.86  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.58/1.86  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.58/1.86  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.58/1.86  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.58/1.86  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.58/1.86  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.58/1.86  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.58/1.86  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.58/1.86  tff(c_88, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.58/1.86  tff(c_92, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_88])).
% 3.58/1.86  tff(c_111, plain, (![A_59, B_60, C_61]: (m1_subset_1(k2_relset_1(A_59, B_60, C_61), k1_zfmisc_1(B_60)) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.58/1.86  tff(c_128, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_111])).
% 3.58/1.86  tff(c_134, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_128])).
% 3.58/1.86  tff(c_6, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.58/1.86  tff(c_137, plain, (![A_3]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_3, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_134, c_6])).
% 3.58/1.86  tff(c_138, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_137])).
% 3.58/1.86  tff(c_46, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.58/1.86  tff(c_94, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_46])).
% 3.58/1.86  tff(c_59, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.58/1.86  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_59])).
% 3.58/1.86  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.58/1.86  tff(c_79, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.58/1.86  tff(c_83, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_79])).
% 3.58/1.86  tff(c_335, plain, (![B_100, A_101, C_102]: (k1_xboole_0=B_100 | k1_relset_1(A_101, B_100, C_102)=A_101 | ~v1_funct_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.86  tff(c_350, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_335])).
% 3.58/1.86  tff(c_356, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_350])).
% 3.58/1.86  tff(c_357, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_356])).
% 3.58/1.86  tff(c_16, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.58/1.86  tff(c_105, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_1'(A_53, B_54, C_55), B_54) | ~r2_hidden(A_53, k9_relat_1(C_55, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.58/1.86  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.58/1.86  tff(c_144, plain, (![A_65, B_66, C_67]: (m1_subset_1('#skF_1'(A_65, B_66, C_67), B_66) | ~r2_hidden(A_65, k9_relat_1(C_67, B_66)) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_105, c_4])).
% 3.58/1.86  tff(c_149, plain, (![A_65, A_12]: (m1_subset_1('#skF_1'(A_65, k1_relat_1(A_12), A_12), k1_relat_1(A_12)) | ~r2_hidden(A_65, k2_relat_1(A_12)) | ~v1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_144])).
% 3.58/1.86  tff(c_365, plain, (![A_65]: (m1_subset_1('#skF_1'(A_65, k1_relat_1('#skF_5'), '#skF_5'), '#skF_3') | ~r2_hidden(A_65, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_357, c_149])).
% 3.58/1.86  tff(c_404, plain, (![A_103]: (m1_subset_1('#skF_1'(A_103, '#skF_3', '#skF_5'), '#skF_3') | ~r2_hidden(A_103, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_357, c_365])).
% 3.58/1.86  tff(c_423, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_94, c_404])).
% 3.58/1.86  tff(c_44, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)!='#skF_2' | ~m1_subset_1(E_32, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.58/1.86  tff(c_427, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_423, c_44])).
% 3.58/1.86  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.58/1.86  tff(c_374, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_357, c_16])).
% 3.58/1.86  tff(c_386, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_374])).
% 3.58/1.86  tff(c_167, plain, (![A_77, B_78, C_79]: (r2_hidden(k4_tarski('#skF_1'(A_77, B_78, C_79), A_77), C_79) | ~r2_hidden(A_77, k9_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.58/1.86  tff(c_20, plain, (![C_15, A_13, B_14]: (k1_funct_1(C_15, A_13)=B_14 | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.58/1.86  tff(c_185, plain, (![C_79, A_77, B_78]: (k1_funct_1(C_79, '#skF_1'(A_77, B_78, C_79))=A_77 | ~v1_funct_1(C_79) | ~r2_hidden(A_77, k9_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_167, c_20])).
% 3.58/1.86  tff(c_394, plain, (![A_77]: (k1_funct_1('#skF_5', '#skF_1'(A_77, '#skF_3', '#skF_5'))=A_77 | ~v1_funct_1('#skF_5') | ~r2_hidden(A_77, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_386, c_185])).
% 3.58/1.86  tff(c_480, plain, (![A_111]: (k1_funct_1('#skF_5', '#skF_1'(A_111, '#skF_3', '#skF_5'))=A_111 | ~r2_hidden(A_111, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_52, c_394])).
% 3.58/1.86  tff(c_495, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(resolution, [status(thm)], [c_94, c_480])).
% 3.58/1.86  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_495])).
% 3.58/1.86  tff(c_503, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_356])).
% 3.58/1.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.58/1.86  tff(c_510, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_2])).
% 3.58/1.86  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_510])).
% 3.58/1.86  tff(c_513, plain, (![A_3]: (~r2_hidden(A_3, k2_relat_1('#skF_5')))), inference(splitRight, [status(thm)], [c_137])).
% 3.58/1.86  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_513, c_94])).
% 3.58/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.86  
% 3.58/1.86  Inference rules
% 3.58/1.86  ----------------------
% 3.58/1.86  #Ref     : 0
% 3.58/1.86  #Sup     : 96
% 3.58/1.86  #Fact    : 0
% 3.58/1.86  #Define  : 0
% 3.58/1.86  #Split   : 4
% 3.58/1.86  #Chain   : 0
% 3.58/1.86  #Close   : 0
% 3.58/1.86  
% 3.58/1.86  Ordering : KBO
% 3.58/1.86  
% 3.58/1.86  Simplification rules
% 3.58/1.86  ----------------------
% 3.58/1.86  #Subsume      : 7
% 3.58/1.86  #Demod        : 43
% 3.58/1.86  #Tautology    : 16
% 3.58/1.86  #SimpNegUnit  : 3
% 3.58/1.86  #BackRed      : 10
% 3.58/1.86  
% 3.58/1.86  #Partial instantiations: 0
% 3.58/1.86  #Strategies tried      : 1
% 3.58/1.86  
% 3.58/1.86  Timing (in seconds)
% 3.58/1.86  ----------------------
% 3.58/1.87  Preprocessing        : 0.55
% 3.58/1.87  Parsing              : 0.29
% 3.58/1.87  CNF conversion       : 0.04
% 3.58/1.87  Main loop            : 0.51
% 3.58/1.87  Inferencing          : 0.18
% 3.58/1.87  Reduction            : 0.15
% 3.58/1.87  Demodulation         : 0.11
% 3.58/1.87  BG Simplification    : 0.03
% 3.58/1.87  Subsumption          : 0.09
% 3.58/1.87  Abstraction          : 0.03
% 3.58/1.87  MUC search           : 0.00
% 3.58/1.87  Cooper               : 0.00
% 3.58/1.87  Total                : 1.11
% 3.58/1.87  Index Insertion      : 0.00
% 3.58/1.87  Index Deletion       : 0.00
% 3.58/1.87  Index Matching       : 0.00
% 3.58/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
