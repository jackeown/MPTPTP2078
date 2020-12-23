%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:00 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 177 expanded)
%              Number of leaves         :   39 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 418 expanded)
%              Number of equality atoms :   33 ( 113 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_95,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relset_1(A_57,B_58,C_59) = k2_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_99,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_50,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_102,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_50])).

tff(c_69,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_73,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_69])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_121,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_125,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_121])).

tff(c_441,plain,(
    ! [B_129,A_130,C_131] :
      ( k1_xboole_0 = B_129
      | k1_relset_1(A_130,B_129,C_131) = A_130
      | ~ v1_funct_2(C_131,A_130,B_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_452,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_441])).

tff(c_457,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_125,c_452])).

tff(c_458,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_14,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_144,plain,(
    ! [A_67,B_68,C_69] :
      ( r2_hidden('#skF_1'(A_67,B_68,C_69),B_68)
      | ~ r2_hidden(A_67,k9_relat_1(C_69,B_68))
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_73,B_74,C_75] :
      ( m1_subset_1('#skF_1'(A_73,B_74,C_75),B_74)
      | ~ r2_hidden(A_73,k9_relat_1(C_75,B_74))
      | ~ v1_relat_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_163,plain,(
    ! [A_73,A_10] :
      ( m1_subset_1('#skF_1'(A_73,k1_relat_1(A_10),A_10),k1_relat_1(A_10))
      | ~ r2_hidden(A_73,k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_158])).

tff(c_463,plain,(
    ! [A_73] :
      ( m1_subset_1('#skF_1'(A_73,'#skF_3','#skF_5'),k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_73,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_163])).

tff(c_510,plain,(
    ! [A_132] :
      ( m1_subset_1('#skF_1'(A_132,'#skF_3','#skF_5'),'#skF_3')
      | ~ r2_hidden(A_132,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_458,c_463])).

tff(c_529,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_510])).

tff(c_48,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) != '#skF_2'
      | ~ m1_subset_1(E_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_552,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_529,c_48])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_478,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_14])).

tff(c_492,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_478])).

tff(c_232,plain,(
    ! [A_101,B_102,C_103] :
      ( r2_hidden(k4_tarski('#skF_1'(A_101,B_102,C_103),A_101),C_103)
      | ~ r2_hidden(A_101,k9_relat_1(C_103,B_102))
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k1_funct_1(C_17,A_15) = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_262,plain,(
    ! [C_103,A_101,B_102] :
      ( k1_funct_1(C_103,'#skF_1'(A_101,B_102,C_103)) = A_101
      | ~ v1_funct_1(C_103)
      | ~ r2_hidden(A_101,k9_relat_1(C_103,B_102))
      | ~ v1_relat_1(C_103) ) ),
    inference(resolution,[status(thm)],[c_232,c_20])).

tff(c_500,plain,(
    ! [A_101] :
      ( k1_funct_1('#skF_5','#skF_1'(A_101,'#skF_3','#skF_5')) = A_101
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_101,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_262])).

tff(c_757,plain,(
    ! [A_152] :
      ( k1_funct_1('#skF_5','#skF_1'(A_152,'#skF_3','#skF_5')) = A_152
      | ~ r2_hidden(A_152,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56,c_500])).

tff(c_776,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_102,c_757])).

tff(c_784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_776])).

tff(c_785,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_798,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_2])).

tff(c_88,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_92,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_88])).

tff(c_16,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,k2_relat_1(B_12))
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_108,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_2',A_11)
      | ~ v5_relat_1('#skF_5',A_11)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_102,c_16])).

tff(c_130,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_2',A_63)
      | ~ v5_relat_1('#skF_5',A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_108])).

tff(c_134,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_130])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_134,c_24])).

tff(c_805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.56  
% 3.26/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.26/1.56  
% 3.26/1.56  %Foreground sorts:
% 3.26/1.56  
% 3.26/1.56  
% 3.26/1.56  %Background operators:
% 3.26/1.56  
% 3.26/1.56  
% 3.26/1.56  %Foreground operators:
% 3.26/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.26/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.26/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.26/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.26/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.26/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.26/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.26/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.26/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.56  
% 3.26/1.58  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.26/1.58  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.26/1.58  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.26/1.58  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.26/1.58  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.26/1.58  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.26/1.58  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.26/1.58  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.26/1.58  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.26/1.58  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.26/1.58  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.26/1.58  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 3.26/1.58  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.26/1.58  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.26/1.58  tff(c_95, plain, (![A_57, B_58, C_59]: (k2_relset_1(A_57, B_58, C_59)=k2_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.26/1.58  tff(c_99, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_95])).
% 3.26/1.58  tff(c_50, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.26/1.58  tff(c_102, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_50])).
% 3.26/1.58  tff(c_69, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.26/1.58  tff(c_73, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_69])).
% 3.26/1.58  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.26/1.58  tff(c_121, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.26/1.58  tff(c_125, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_121])).
% 3.26/1.58  tff(c_441, plain, (![B_129, A_130, C_131]: (k1_xboole_0=B_129 | k1_relset_1(A_130, B_129, C_131)=A_130 | ~v1_funct_2(C_131, A_130, B_129) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.26/1.58  tff(c_452, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_441])).
% 3.26/1.58  tff(c_457, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_125, c_452])).
% 3.26/1.58  tff(c_458, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_457])).
% 3.26/1.58  tff(c_14, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.26/1.58  tff(c_144, plain, (![A_67, B_68, C_69]: (r2_hidden('#skF_1'(A_67, B_68, C_69), B_68) | ~r2_hidden(A_67, k9_relat_1(C_69, B_68)) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.26/1.58  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.58  tff(c_158, plain, (![A_73, B_74, C_75]: (m1_subset_1('#skF_1'(A_73, B_74, C_75), B_74) | ~r2_hidden(A_73, k9_relat_1(C_75, B_74)) | ~v1_relat_1(C_75))), inference(resolution, [status(thm)], [c_144, c_4])).
% 3.26/1.58  tff(c_163, plain, (![A_73, A_10]: (m1_subset_1('#skF_1'(A_73, k1_relat_1(A_10), A_10), k1_relat_1(A_10)) | ~r2_hidden(A_73, k2_relat_1(A_10)) | ~v1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_158])).
% 3.26/1.58  tff(c_463, plain, (![A_73]: (m1_subset_1('#skF_1'(A_73, '#skF_3', '#skF_5'), k1_relat_1('#skF_5')) | ~r2_hidden(A_73, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_458, c_163])).
% 3.26/1.58  tff(c_510, plain, (![A_132]: (m1_subset_1('#skF_1'(A_132, '#skF_3', '#skF_5'), '#skF_3') | ~r2_hidden(A_132, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_458, c_463])).
% 3.26/1.58  tff(c_529, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_102, c_510])).
% 3.26/1.58  tff(c_48, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)!='#skF_2' | ~m1_subset_1(E_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.26/1.58  tff(c_552, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_529, c_48])).
% 3.26/1.58  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.26/1.58  tff(c_478, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_458, c_14])).
% 3.26/1.58  tff(c_492, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_478])).
% 3.26/1.58  tff(c_232, plain, (![A_101, B_102, C_103]: (r2_hidden(k4_tarski('#skF_1'(A_101, B_102, C_103), A_101), C_103) | ~r2_hidden(A_101, k9_relat_1(C_103, B_102)) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.26/1.58  tff(c_20, plain, (![C_17, A_15, B_16]: (k1_funct_1(C_17, A_15)=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.26/1.58  tff(c_262, plain, (![C_103, A_101, B_102]: (k1_funct_1(C_103, '#skF_1'(A_101, B_102, C_103))=A_101 | ~v1_funct_1(C_103) | ~r2_hidden(A_101, k9_relat_1(C_103, B_102)) | ~v1_relat_1(C_103))), inference(resolution, [status(thm)], [c_232, c_20])).
% 3.26/1.58  tff(c_500, plain, (![A_101]: (k1_funct_1('#skF_5', '#skF_1'(A_101, '#skF_3', '#skF_5'))=A_101 | ~v1_funct_1('#skF_5') | ~r2_hidden(A_101, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_492, c_262])).
% 3.26/1.58  tff(c_757, plain, (![A_152]: (k1_funct_1('#skF_5', '#skF_1'(A_152, '#skF_3', '#skF_5'))=A_152 | ~r2_hidden(A_152, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56, c_500])).
% 3.26/1.58  tff(c_776, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(resolution, [status(thm)], [c_102, c_757])).
% 3.26/1.58  tff(c_784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_552, c_776])).
% 3.26/1.58  tff(c_785, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_457])).
% 3.26/1.58  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.58  tff(c_798, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_785, c_2])).
% 3.26/1.58  tff(c_88, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.26/1.58  tff(c_92, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_88])).
% 3.26/1.58  tff(c_16, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, k2_relat_1(B_12)) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.58  tff(c_108, plain, (![A_11]: (r2_hidden('#skF_2', A_11) | ~v5_relat_1('#skF_5', A_11) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_102, c_16])).
% 3.26/1.58  tff(c_130, plain, (![A_63]: (r2_hidden('#skF_2', A_63) | ~v5_relat_1('#skF_5', A_63))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_108])).
% 3.26/1.58  tff(c_134, plain, (r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_92, c_130])).
% 3.26/1.58  tff(c_24, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.26/1.58  tff(c_142, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_134, c_24])).
% 3.26/1.58  tff(c_805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_798, c_142])).
% 3.26/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.58  
% 3.26/1.58  Inference rules
% 3.26/1.58  ----------------------
% 3.26/1.58  #Ref     : 0
% 3.26/1.58  #Sup     : 157
% 3.26/1.58  #Fact    : 0
% 3.26/1.58  #Define  : 0
% 3.26/1.58  #Split   : 3
% 3.26/1.58  #Chain   : 0
% 3.26/1.58  #Close   : 0
% 3.26/1.58  
% 3.26/1.58  Ordering : KBO
% 3.26/1.58  
% 3.26/1.58  Simplification rules
% 3.26/1.58  ----------------------
% 3.26/1.58  #Subsume      : 12
% 3.26/1.58  #Demod        : 58
% 3.26/1.58  #Tautology    : 18
% 3.26/1.58  #SimpNegUnit  : 1
% 3.26/1.58  #BackRed      : 17
% 3.26/1.58  
% 3.26/1.58  #Partial instantiations: 0
% 3.26/1.58  #Strategies tried      : 1
% 3.26/1.58  
% 3.26/1.58  Timing (in seconds)
% 3.26/1.58  ----------------------
% 3.26/1.58  Preprocessing        : 0.35
% 3.26/1.58  Parsing              : 0.19
% 3.26/1.59  CNF conversion       : 0.02
% 3.26/1.59  Main loop            : 0.41
% 3.26/1.59  Inferencing          : 0.14
% 3.26/1.59  Reduction            : 0.12
% 3.26/1.59  Demodulation         : 0.09
% 3.26/1.59  BG Simplification    : 0.03
% 3.26/1.59  Subsumption          : 0.08
% 3.26/1.59  Abstraction          : 0.02
% 3.26/1.59  MUC search           : 0.00
% 3.26/1.59  Cooper               : 0.00
% 3.26/1.59  Total                : 0.80
% 3.26/1.59  Index Insertion      : 0.00
% 3.26/1.59  Index Deletion       : 0.00
% 3.26/1.59  Index Matching       : 0.00
% 3.26/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
