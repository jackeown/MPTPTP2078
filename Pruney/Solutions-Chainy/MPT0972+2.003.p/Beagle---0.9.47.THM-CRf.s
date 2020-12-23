%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:35 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 855 expanded)
%              Number of leaves         :   31 ( 292 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 (2346 expanded)
%              Number of equality atoms :   72 ( 546 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_210,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r2_relset_1(A_65,B_66,C_67,C_67)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_223,plain,(
    ! [C_69] :
      ( r2_relset_1('#skF_2','#skF_3',C_69,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_210])).

tff(c_228,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_223])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_108,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_120,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_108])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_125,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_139,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_125])).

tff(c_170,plain,(
    ! [B_62,A_63,C_64] :
      ( k1_xboole_0 = B_62
      | k1_relset_1(A_63,B_62,C_64) = A_63
      | ~ v1_funct_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_176,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_170])).

tff(c_188,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_139,c_176])).

tff(c_196,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_119,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_108])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_138,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_125])).

tff(c_173,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_170])).

tff(c_185,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_138,c_173])).

tff(c_190,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_230,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),k1_relat_1(A_70))
      | B_71 = A_70
      | k1_relat_1(B_71) != k1_relat_1(A_70)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_236,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_1'('#skF_4',B_71),'#skF_2')
      | B_71 = '#skF_4'
      | k1_relat_1(B_71) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_230])).

tff(c_248,plain,(
    ! [B_74] :
      ( r2_hidden('#skF_1'('#skF_4',B_74),'#skF_2')
      | B_74 = '#skF_4'
      | k1_relat_1(B_74) != '#skF_2'
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_50,c_190,c_236])).

tff(c_38,plain,(
    ! [E_31] :
      ( k1_funct_1('#skF_5',E_31) = k1_funct_1('#skF_4',E_31)
      | ~ r2_hidden(E_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_252,plain,(
    ! [B_74] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_74)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_74))
      | B_74 = '#skF_4'
      | k1_relat_1(B_74) != '#skF_2'
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_248,c_38])).

tff(c_276,plain,(
    ! [B_77,A_78] :
      ( k1_funct_1(B_77,'#skF_1'(A_78,B_77)) != k1_funct_1(A_78,'#skF_1'(A_78,B_77))
      | B_77 = A_78
      | k1_relat_1(B_77) != k1_relat_1(A_78)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_280,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_276])).

tff(c_286,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_44,c_196,c_119,c_50,c_196,c_190,c_280])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_298,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_36])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_298])).

tff(c_309,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_324,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_322,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_8])).

tff(c_87,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_87])).

tff(c_96,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_336,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_96])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_336])).

tff(c_342,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_357,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_2])).

tff(c_355,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_342,c_8])).

tff(c_387,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_96])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_387])).

tff(c_394,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_393,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_77,plain,(
    ! [B_34,A_35] :
      ( ~ v1_xboole_0(B_34)
      | B_34 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_400,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_393,c_80])).

tff(c_415,plain,(
    ! [A_85] :
      ( A_85 = '#skF_4'
      | ~ v1_xboole_0(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_80])).

tff(c_422,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_394,c_415])).

tff(c_460,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_46])).

tff(c_404,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_8])).

tff(c_809,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( r2_relset_1(A_153,B_154,C_155,C_155)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_813,plain,(
    ! [A_3,C_155,D_156] :
      ( r2_relset_1(A_3,'#skF_4',C_155,C_155)
      | ~ m1_subset_1(D_156,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_3,'#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_809])).

tff(c_815,plain,(
    ! [A_3,C_155,D_156] :
      ( r2_relset_1(A_3,'#skF_4',C_155,C_155)
      | ~ m1_subset_1(D_156,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_155,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_813])).

tff(c_826,plain,(
    ! [D_156] : ~ m1_subset_1(D_156,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_815])).

tff(c_834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_826,c_460])).

tff(c_836,plain,(
    ! [A_164,C_165] :
      ( r2_relset_1(A_164,'#skF_4',C_165,C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_815])).

tff(c_839,plain,(
    ! [A_164] : r2_relset_1(A_164,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_460,c_836])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_405,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_10])).

tff(c_668,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( r2_relset_1(A_118,B_119,C_120,C_120)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_670,plain,(
    ! [B_4,C_120,D_121] :
      ( r2_relset_1('#skF_4',B_4,C_120,C_120)
      | ~ m1_subset_1(D_121,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_4))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_668])).

tff(c_673,plain,(
    ! [B_4,C_120,D_121] :
      ( r2_relset_1('#skF_4',B_4,C_120,C_120)
      | ~ m1_subset_1(D_121,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_120,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_670])).

tff(c_675,plain,(
    ! [D_121] : ~ m1_subset_1(D_121,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_673])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_675,c_460])).

tff(c_688,plain,(
    ! [B_125,C_126] :
      ( r2_relset_1('#skF_4',B_125,C_126,C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_691,plain,(
    ! [B_125] : r2_relset_1('#skF_4',B_125,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_460,c_688])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_447,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_4'
      | A_3 = '#skF_4'
      | k2_zfmisc_1(A_3,B_4) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_400,c_6])).

tff(c_469,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_447])).

tff(c_504,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_461,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_40])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_479,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_461,c_12])).

tff(c_482,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_479])).

tff(c_403,plain,(
    ! [A_35] :
      ( A_35 = '#skF_4'
      | ~ v1_xboole_0(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_80])).

tff(c_488,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_482,c_403])).

tff(c_493,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_36])).

tff(c_518,plain,(
    ~ r2_relset_1('#skF_4','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_493])).

tff(c_694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_518])).

tff(c_695,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_705,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_493])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:14:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.15/1.48  
% 3.15/1.48  %Foreground sorts:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Background operators:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Foreground operators:
% 3.15/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.15/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.48  
% 3.15/1.51  tff(f_118, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 3.15/1.51  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.15/1.51  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.15/1.51  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.15/1.51  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.15/1.51  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 3.15/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.15/1.51  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.15/1.51  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.15/1.51  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.15/1.51  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.51  tff(c_210, plain, (![A_65, B_66, C_67, D_68]: (r2_relset_1(A_65, B_66, C_67, C_67) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.51  tff(c_223, plain, (![C_69]: (r2_relset_1('#skF_2', '#skF_3', C_69, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_46, c_210])).
% 3.15/1.51  tff(c_228, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_223])).
% 3.15/1.51  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.51  tff(c_108, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.51  tff(c_120, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_108])).
% 3.15/1.51  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.51  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.51  tff(c_125, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.15/1.51  tff(c_139, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_125])).
% 3.15/1.51  tff(c_170, plain, (![B_62, A_63, C_64]: (k1_xboole_0=B_62 | k1_relset_1(A_63, B_62, C_64)=A_63 | ~v1_funct_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.15/1.51  tff(c_176, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_170])).
% 3.15/1.51  tff(c_188, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_139, c_176])).
% 3.15/1.51  tff(c_196, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_188])).
% 3.15/1.51  tff(c_119, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_108])).
% 3.15/1.51  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.51  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.51  tff(c_138, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_125])).
% 3.15/1.51  tff(c_173, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_170])).
% 3.15/1.51  tff(c_185, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_138, c_173])).
% 3.15/1.51  tff(c_190, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_185])).
% 3.15/1.51  tff(c_230, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), k1_relat_1(A_70)) | B_71=A_70 | k1_relat_1(B_71)!=k1_relat_1(A_70) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.51  tff(c_236, plain, (![B_71]: (r2_hidden('#skF_1'('#skF_4', B_71), '#skF_2') | B_71='#skF_4' | k1_relat_1(B_71)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_71) | ~v1_relat_1(B_71) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_230])).
% 3.15/1.51  tff(c_248, plain, (![B_74]: (r2_hidden('#skF_1'('#skF_4', B_74), '#skF_2') | B_74='#skF_4' | k1_relat_1(B_74)!='#skF_2' | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_50, c_190, c_236])).
% 3.15/1.51  tff(c_38, plain, (![E_31]: (k1_funct_1('#skF_5', E_31)=k1_funct_1('#skF_4', E_31) | ~r2_hidden(E_31, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.51  tff(c_252, plain, (![B_74]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_74))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_74)) | B_74='#skF_4' | k1_relat_1(B_74)!='#skF_2' | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_248, c_38])).
% 3.15/1.51  tff(c_276, plain, (![B_77, A_78]: (k1_funct_1(B_77, '#skF_1'(A_78, B_77))!=k1_funct_1(A_78, '#skF_1'(A_78, B_77)) | B_77=A_78 | k1_relat_1(B_77)!=k1_relat_1(A_78) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.51  tff(c_280, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_252, c_276])).
% 3.15/1.51  tff(c_286, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_44, c_196, c_119, c_50, c_196, c_190, c_280])).
% 3.15/1.51  tff(c_36, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.51  tff(c_298, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_36])).
% 3.15/1.51  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_298])).
% 3.15/1.51  tff(c_309, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_188])).
% 3.15/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.15/1.51  tff(c_324, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_2])).
% 3.15/1.51  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.51  tff(c_322, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_8])).
% 3.15/1.51  tff(c_87, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.51  tff(c_94, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_87])).
% 3.15/1.51  tff(c_96, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_94])).
% 3.15/1.51  tff(c_336, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_96])).
% 3.15/1.51  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_324, c_336])).
% 3.15/1.51  tff(c_342, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_185])).
% 3.15/1.51  tff(c_357, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_2])).
% 3.15/1.51  tff(c_355, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_342, c_8])).
% 3.15/1.51  tff(c_387, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_96])).
% 3.15/1.51  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_387])).
% 3.15/1.51  tff(c_394, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_94])).
% 3.15/1.51  tff(c_393, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_94])).
% 3.15/1.51  tff(c_77, plain, (![B_34, A_35]: (~v1_xboole_0(B_34) | B_34=A_35 | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.15/1.51  tff(c_80, plain, (![A_35]: (k1_xboole_0=A_35 | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_2, c_77])).
% 3.15/1.51  tff(c_400, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_393, c_80])).
% 3.15/1.51  tff(c_415, plain, (![A_85]: (A_85='#skF_4' | ~v1_xboole_0(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_80])).
% 3.15/1.51  tff(c_422, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_394, c_415])).
% 3.15/1.51  tff(c_460, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_46])).
% 3.15/1.51  tff(c_404, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_8])).
% 3.15/1.51  tff(c_809, plain, (![A_153, B_154, C_155, D_156]: (r2_relset_1(A_153, B_154, C_155, C_155) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.51  tff(c_813, plain, (![A_3, C_155, D_156]: (r2_relset_1(A_3, '#skF_4', C_155, C_155) | ~m1_subset_1(D_156, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_3, '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_404, c_809])).
% 3.15/1.51  tff(c_815, plain, (![A_3, C_155, D_156]: (r2_relset_1(A_3, '#skF_4', C_155, C_155) | ~m1_subset_1(D_156, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_155, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_813])).
% 3.15/1.51  tff(c_826, plain, (![D_156]: (~m1_subset_1(D_156, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_815])).
% 3.15/1.51  tff(c_834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_826, c_460])).
% 3.15/1.51  tff(c_836, plain, (![A_164, C_165]: (r2_relset_1(A_164, '#skF_4', C_165, C_165) | ~m1_subset_1(C_165, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_815])).
% 3.15/1.51  tff(c_839, plain, (![A_164]: (r2_relset_1(A_164, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_460, c_836])).
% 3.15/1.51  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.51  tff(c_405, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_10])).
% 3.15/1.51  tff(c_668, plain, (![A_118, B_119, C_120, D_121]: (r2_relset_1(A_118, B_119, C_120, C_120) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.51  tff(c_670, plain, (![B_4, C_120, D_121]: (r2_relset_1('#skF_4', B_4, C_120, C_120) | ~m1_subset_1(D_121, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_4))))), inference(superposition, [status(thm), theory('equality')], [c_405, c_668])).
% 3.15/1.51  tff(c_673, plain, (![B_4, C_120, D_121]: (r2_relset_1('#skF_4', B_4, C_120, C_120) | ~m1_subset_1(D_121, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_120, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_670])).
% 3.15/1.51  tff(c_675, plain, (![D_121]: (~m1_subset_1(D_121, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_673])).
% 3.15/1.51  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_675, c_460])).
% 3.15/1.51  tff(c_688, plain, (![B_125, C_126]: (r2_relset_1('#skF_4', B_125, C_126, C_126) | ~m1_subset_1(C_126, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_673])).
% 3.15/1.51  tff(c_691, plain, (![B_125]: (r2_relset_1('#skF_4', B_125, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_460, c_688])).
% 3.15/1.51  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.51  tff(c_447, plain, (![B_4, A_3]: (B_4='#skF_4' | A_3='#skF_4' | k2_zfmisc_1(A_3, B_4)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_400, c_6])).
% 3.15/1.51  tff(c_469, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_422, c_447])).
% 3.15/1.51  tff(c_504, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_469])).
% 3.15/1.51  tff(c_461, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_40])).
% 3.15/1.51  tff(c_12, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.51  tff(c_479, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_461, c_12])).
% 3.15/1.51  tff(c_482, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_393, c_479])).
% 3.15/1.51  tff(c_403, plain, (![A_35]: (A_35='#skF_4' | ~v1_xboole_0(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_80])).
% 3.15/1.51  tff(c_488, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_482, c_403])).
% 3.15/1.51  tff(c_493, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_36])).
% 3.15/1.51  tff(c_518, plain, (~r2_relset_1('#skF_4', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_493])).
% 3.15/1.51  tff(c_694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_691, c_518])).
% 3.15/1.51  tff(c_695, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_469])).
% 3.15/1.51  tff(c_705, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_493])).
% 3.15/1.51  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_839, c_705])).
% 3.15/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.51  
% 3.15/1.51  Inference rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Ref     : 2
% 3.15/1.51  #Sup     : 160
% 3.15/1.51  #Fact    : 0
% 3.15/1.51  #Define  : 0
% 3.15/1.51  #Split   : 11
% 3.15/1.51  #Chain   : 0
% 3.15/1.51  #Close   : 0
% 3.15/1.51  
% 3.15/1.51  Ordering : KBO
% 3.15/1.51  
% 3.15/1.51  Simplification rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Subsume      : 44
% 3.15/1.51  #Demod        : 243
% 3.15/1.51  #Tautology    : 112
% 3.15/1.51  #SimpNegUnit  : 7
% 3.15/1.51  #BackRed      : 68
% 3.15/1.51  
% 3.15/1.51  #Partial instantiations: 0
% 3.15/1.51  #Strategies tried      : 1
% 3.15/1.51  
% 3.15/1.51  Timing (in seconds)
% 3.15/1.51  ----------------------
% 3.15/1.51  Preprocessing        : 0.34
% 3.15/1.51  Parsing              : 0.19
% 3.15/1.51  CNF conversion       : 0.02
% 3.15/1.51  Main loop            : 0.37
% 3.15/1.51  Inferencing          : 0.12
% 3.15/1.51  Reduction            : 0.12
% 3.15/1.51  Demodulation         : 0.08
% 3.15/1.51  BG Simplification    : 0.02
% 3.15/1.51  Subsumption          : 0.07
% 3.15/1.51  Abstraction          : 0.02
% 3.15/1.51  MUC search           : 0.00
% 3.15/1.51  Cooper               : 0.00
% 3.15/1.51  Total                : 0.75
% 3.15/1.51  Index Insertion      : 0.00
% 3.15/1.51  Index Deletion       : 0.00
% 3.15/1.51  Index Matching       : 0.00
% 3.15/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
