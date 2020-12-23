%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:28 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 197 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 633 expanded)
%              Number of equality atoms :   19 (  92 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_85,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_40,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22])).

tff(c_255,plain,(
    ! [D_63,E_66,C_62,B_64,A_67,F_65] :
      ( m1_subset_1(k1_partfun1(A_67,B_64,C_62,D_63,E_66,F_65),k1_zfmisc_1(k2_zfmisc_1(A_67,D_63)))
      | ~ m1_subset_1(F_65,k1_zfmisc_1(k2_zfmisc_1(C_62,D_63)))
      | ~ v1_funct_1(F_65)
      | ~ m1_subset_1(E_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_64)))
      | ~ v1_funct_1(E_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [A_14] : m1_subset_1(k6_relat_1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28])).

tff(c_42,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_189,plain,(
    ! [D_45,C_46,A_47,B_48] :
      ( D_45 = C_46
      | ~ r2_relset_1(A_47,B_48,C_46,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_193,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_189])).

tff(c_200,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_193])).

tff(c_218,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_260,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_218])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_48,c_44,c_260])).

tff(c_277,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_480,plain,(
    ! [B_126,A_122,E_123,D_125,C_124] :
      ( k1_xboole_0 = C_124
      | v2_funct_1(D_125)
      | ~ v2_funct_1(k1_partfun1(A_122,B_126,B_126,C_124,D_125,E_123))
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(B_126,C_124)))
      | ~ v1_funct_2(E_123,B_126,C_124)
      | ~ v1_funct_1(E_123)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_122,B_126)))
      | ~ v1_funct_2(D_125,A_122,B_126)
      | ~ v1_funct_1(D_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_482,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_480])).

tff(c_487,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_48,c_46,c_44,c_58,c_482])).

tff(c_488,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_487])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_513,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_2])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_511,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_488,c_8])).

tff(c_113,plain,(
    ! [A_36] :
      ( v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_113,c_40])).

tff(c_119,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_116])).

tff(c_120,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_121,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_121])).

tff(c_140,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_130])).

tff(c_540,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_140])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_540])).

tff(c_545,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_546,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_560,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_546,c_12])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.43  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.07/1.43  
% 3.07/1.43  %Foreground sorts:
% 3.07/1.43  
% 3.07/1.43  
% 3.07/1.43  %Background operators:
% 3.07/1.43  
% 3.07/1.43  
% 3.07/1.43  %Foreground operators:
% 3.07/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.07/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.43  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.43  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.43  
% 3.07/1.45  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 3.07/1.45  tff(f_85, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.07/1.45  tff(f_61, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 3.07/1.45  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.07/1.45  tff(f_71, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.07/1.45  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.07/1.45  tff(f_107, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.07/1.45  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.07/1.45  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.07/1.45  tff(f_59, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.07/1.45  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.07/1.45  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.07/1.45  tff(c_40, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.07/1.45  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.07/1.45  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.07/1.45  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.07/1.45  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.07/1.45  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.07/1.45  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.07/1.45  tff(c_34, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.07/1.45  tff(c_22, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.07/1.45  tff(c_58, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_22])).
% 3.07/1.45  tff(c_255, plain, (![D_63, E_66, C_62, B_64, A_67, F_65]: (m1_subset_1(k1_partfun1(A_67, B_64, C_62, D_63, E_66, F_65), k1_zfmisc_1(k2_zfmisc_1(A_67, D_63))) | ~m1_subset_1(F_65, k1_zfmisc_1(k2_zfmisc_1(C_62, D_63))) | ~v1_funct_1(F_65) | ~m1_subset_1(E_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_64))) | ~v1_funct_1(E_66))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.07/1.45  tff(c_28, plain, (![A_14]: (m1_subset_1(k6_relat_1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.45  tff(c_57, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28])).
% 3.07/1.45  tff(c_42, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.07/1.45  tff(c_189, plain, (![D_45, C_46, A_47, B_48]: (D_45=C_46 | ~r2_relset_1(A_47, B_48, C_46, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.07/1.45  tff(c_193, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_42, c_189])).
% 3.07/1.45  tff(c_200, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_193])).
% 3.07/1.45  tff(c_218, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_200])).
% 3.07/1.45  tff(c_260, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_255, c_218])).
% 3.07/1.45  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_48, c_44, c_260])).
% 3.07/1.45  tff(c_277, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_200])).
% 3.07/1.45  tff(c_480, plain, (![B_126, A_122, E_123, D_125, C_124]: (k1_xboole_0=C_124 | v2_funct_1(D_125) | ~v2_funct_1(k1_partfun1(A_122, B_126, B_126, C_124, D_125, E_123)) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(B_126, C_124))) | ~v1_funct_2(E_123, B_126, C_124) | ~v1_funct_1(E_123) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_122, B_126))) | ~v1_funct_2(D_125, A_122, B_126) | ~v1_funct_1(D_125))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.07/1.45  tff(c_482, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_277, c_480])).
% 3.07/1.45  tff(c_487, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_48, c_46, c_44, c_58, c_482])).
% 3.07/1.45  tff(c_488, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_40, c_487])).
% 3.07/1.45  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.07/1.45  tff(c_513, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_2])).
% 3.07/1.45  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.45  tff(c_511, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_488, c_8])).
% 3.07/1.45  tff(c_113, plain, (![A_36]: (v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.07/1.45  tff(c_116, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_113, c_40])).
% 3.07/1.45  tff(c_119, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_116])).
% 3.07/1.45  tff(c_120, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_119])).
% 3.07/1.45  tff(c_121, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.07/1.45  tff(c_130, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_121])).
% 3.07/1.45  tff(c_140, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_120, c_130])).
% 3.07/1.45  tff(c_540, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_140])).
% 3.07/1.45  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_513, c_540])).
% 3.07/1.45  tff(c_545, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_119])).
% 3.07/1.45  tff(c_546, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_119])).
% 3.07/1.45  tff(c_12, plain, (![A_6]: (v1_relat_1(A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.45  tff(c_560, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_546, c_12])).
% 3.07/1.45  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_545, c_560])).
% 3.07/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.45  
% 3.07/1.45  Inference rules
% 3.07/1.45  ----------------------
% 3.07/1.45  #Ref     : 0
% 3.07/1.45  #Sup     : 104
% 3.07/1.45  #Fact    : 0
% 3.07/1.45  #Define  : 0
% 3.07/1.45  #Split   : 3
% 3.07/1.45  #Chain   : 0
% 3.07/1.45  #Close   : 0
% 3.07/1.45  
% 3.07/1.45  Ordering : KBO
% 3.07/1.45  
% 3.07/1.45  Simplification rules
% 3.07/1.45  ----------------------
% 3.07/1.45  #Subsume      : 0
% 3.07/1.45  #Demod        : 119
% 3.07/1.45  #Tautology    : 36
% 3.07/1.45  #SimpNegUnit  : 3
% 3.07/1.45  #BackRed      : 28
% 3.07/1.45  
% 3.07/1.45  #Partial instantiations: 0
% 3.07/1.45  #Strategies tried      : 1
% 3.07/1.45  
% 3.07/1.45  Timing (in seconds)
% 3.07/1.45  ----------------------
% 3.07/1.45  Preprocessing        : 0.33
% 3.07/1.45  Parsing              : 0.17
% 3.07/1.45  CNF conversion       : 0.02
% 3.07/1.45  Main loop            : 0.34
% 3.07/1.45  Inferencing          : 0.12
% 3.07/1.45  Reduction            : 0.12
% 3.07/1.45  Demodulation         : 0.09
% 3.07/1.45  BG Simplification    : 0.02
% 3.07/1.45  Subsumption          : 0.06
% 3.07/1.45  Abstraction          : 0.01
% 3.07/1.46  MUC search           : 0.00
% 3.07/1.46  Cooper               : 0.00
% 3.07/1.46  Total                : 0.71
% 3.07/1.46  Index Insertion      : 0.00
% 3.07/1.46  Index Deletion       : 0.00
% 3.07/1.46  Index Matching       : 0.00
% 3.07/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
