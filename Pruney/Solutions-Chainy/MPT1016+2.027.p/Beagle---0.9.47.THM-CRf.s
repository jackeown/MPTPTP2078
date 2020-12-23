%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:44 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 500 expanded)
%              Number of leaves         :   30 ( 186 expanded)
%              Depth                    :   11
%              Number of atoms          :  229 (1675 expanded)
%              Number of equality atoms :   83 ( 599 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_61,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_67,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,(
    ! [A_31] :
      ( '#skF_2'(A_31) != '#skF_1'(A_31)
      | v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_59,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_71,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_59])).

tff(c_74,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_38,c_71])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_77,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_161,plain,(
    ! [B_54,A_55,C_56] :
      ( k1_xboole_0 = B_54
      | k1_relset_1(A_55,B_54,C_56) = A_55
      | ~ v1_funct_2(C_56,A_55,B_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_164,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_161])).

tff(c_167,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_81,c_164])).

tff(c_168,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_14,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_14])).

tff(c_183,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_38,c_176])).

tff(c_184,plain,(
    r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_183])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_12])).

tff(c_180,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_38,c_173])).

tff(c_181,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_180])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_funct_1(A_6,'#skF_2'(A_6)) = k1_funct_1(A_6,'#skF_1'(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [D_26,C_25] :
      ( v2_funct_1('#skF_4')
      | D_26 = C_25
      | k1_funct_1('#skF_4',D_26) != k1_funct_1('#skF_4',C_25)
      | ~ r2_hidden(D_26,'#skF_3')
      | ~ r2_hidden(C_25,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_101,plain,(
    ! [D_39,C_40] :
      ( D_39 = C_40
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4',C_40)
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden(C_40,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_58])).

tff(c_107,plain,(
    ! [D_39] :
      ( D_39 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_112,plain,(
    ! [D_39] :
      ( D_39 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_38,c_107])).

tff(c_113,plain,(
    ! [D_39] :
      ( D_39 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_112])).

tff(c_208,plain,(
    ! [D_39] :
      ( D_39 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_39) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_39,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_113])).

tff(c_211,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_208])).

tff(c_213,plain,(
    '#skF_2'('#skF_4') = '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_211])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_213])).

tff(c_217,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_216,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_30,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1(k1_xboole_0,B_19,C_20) = k1_xboole_0
      | ~ v1_funct_2(C_20,k1_xboole_0,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_261,plain,(
    ! [B_68,C_69] :
      ( k1_relset_1('#skF_3',B_68,C_69) = '#skF_3'
      | ~ v1_funct_2(C_69,'#skF_3',B_68)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_68))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_216,c_216,c_30])).

tff(c_264,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_261])).

tff(c_267,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_81,c_264])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_267])).

tff(c_271,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_274,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_44])).

tff(c_294,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_298,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_294])).

tff(c_455,plain,(
    ! [B_105,A_106,C_107] :
      ( k1_xboole_0 = B_105
      | k1_relset_1(A_106,B_105,C_107) = A_106
      | ~ v1_funct_2(C_107,A_106,B_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_458,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_455])).

tff(c_461,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_298,c_458])).

tff(c_462,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_270,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_277,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_280,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_277])).

tff(c_283,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_280])).

tff(c_46,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_276,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_46])).

tff(c_368,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_371,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_368])).

tff(c_374,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_298,c_371])).

tff(c_375,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_42,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_285,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_42])).

tff(c_323,plain,(
    ! [B_91,A_92] :
      ( k1_funct_1(k2_funct_1(B_91),k1_funct_1(B_91,A_92)) = A_92
      | ~ r2_hidden(A_92,k1_relat_1(B_91))
      | ~ v2_funct_1(B_91)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_341,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_323])).

tff(c_345,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_38,c_271,c_341])).

tff(c_346,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_376,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_346])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_376])).

tff(c_382,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_381,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_403,plain,(
    ! [B_101,C_102] :
      ( k1_relset_1('#skF_3',B_101,C_102) = '#skF_3'
      | ~ v1_funct_2(C_102,'#skF_3',B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_101))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_381,c_381,c_381,c_30])).

tff(c_406,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_403])).

tff(c_409,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_298,c_406])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_409])).

tff(c_412,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k1_funct_1(k2_funct_1(B_14),k1_funct_1(B_14,A_13)) = A_13
      | ~ r2_hidden(A_13,k1_relat_1(B_14))
      | ~ v2_funct_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_421,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_18])).

tff(c_428,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_38,c_271,c_421])).

tff(c_429,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_428])).

tff(c_463,plain,(
    ~ r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_429])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_463])).

tff(c_470,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_469,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_547,plain,(
    ! [B_117,C_118] :
      ( k1_relset_1('#skF_3',B_117,C_118) = '#skF_3'
      | ~ v1_funct_2(C_118,'#skF_3',B_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_117))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_469,c_469,c_469,c_30])).

tff(c_550,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_547])).

tff(c_553,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_298,c_550])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.44  
% 2.60/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.44  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.60/1.44  
% 2.60/1.44  %Foreground sorts:
% 2.60/1.44  
% 2.60/1.44  
% 2.60/1.44  %Background operators:
% 2.60/1.44  
% 2.60/1.44  
% 2.60/1.44  %Foreground operators:
% 2.60/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.60/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.60/1.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.60/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.60/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.60/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.60/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.60/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.60/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.44  
% 2.60/1.46  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.60/1.46  tff(f_101, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 2.60/1.46  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.60/1.46  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.60/1.46  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.60/1.46  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.60/1.46  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 2.60/1.46  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.60/1.46  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.46  tff(c_61, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.46  tff(c_64, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_61])).
% 2.60/1.46  tff(c_67, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 2.60/1.46  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.46  tff(c_68, plain, (![A_31]: ('#skF_2'(A_31)!='#skF_1'(A_31) | v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.46  tff(c_40, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.46  tff(c_59, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 2.60/1.46  tff(c_71, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_59])).
% 2.60/1.46  tff(c_74, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_38, c_71])).
% 2.60/1.46  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.46  tff(c_77, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.46  tff(c_81, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_77])).
% 2.60/1.46  tff(c_161, plain, (![B_54, A_55, C_56]: (k1_xboole_0=B_54 | k1_relset_1(A_55, B_54, C_56)=A_55 | ~v1_funct_2(C_56, A_55, B_54) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.60/1.46  tff(c_164, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_161])).
% 2.60/1.46  tff(c_167, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_81, c_164])).
% 2.60/1.46  tff(c_168, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_167])).
% 2.60/1.46  tff(c_14, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.46  tff(c_176, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_168, c_14])).
% 2.60/1.46  tff(c_183, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_38, c_176])).
% 2.60/1.46  tff(c_184, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_59, c_183])).
% 2.60/1.46  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.46  tff(c_173, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_168, c_12])).
% 2.60/1.46  tff(c_180, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_38, c_173])).
% 2.60/1.46  tff(c_181, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_59, c_180])).
% 2.60/1.46  tff(c_10, plain, (![A_6]: (k1_funct_1(A_6, '#skF_2'(A_6))=k1_funct_1(A_6, '#skF_1'(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.46  tff(c_58, plain, (![D_26, C_25]: (v2_funct_1('#skF_4') | D_26=C_25 | k1_funct_1('#skF_4', D_26)!=k1_funct_1('#skF_4', C_25) | ~r2_hidden(D_26, '#skF_3') | ~r2_hidden(C_25, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.46  tff(c_101, plain, (![D_39, C_40]: (D_39=C_40 | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', C_40) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden(C_40, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_59, c_58])).
% 2.60/1.46  tff(c_107, plain, (![D_39]: (D_39='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_101])).
% 2.60/1.46  tff(c_112, plain, (![D_39]: (D_39='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_38, c_107])).
% 2.60/1.46  tff(c_113, plain, (![D_39]: (D_39='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_39, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_59, c_112])).
% 2.60/1.46  tff(c_208, plain, (![D_39]: (D_39='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_39)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_39, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_113])).
% 2.60/1.46  tff(c_211, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_208])).
% 2.60/1.46  tff(c_213, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_211])).
% 2.60/1.46  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_213])).
% 2.60/1.46  tff(c_217, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_167])).
% 2.60/1.46  tff(c_216, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_167])).
% 2.60/1.46  tff(c_30, plain, (![B_19, C_20]: (k1_relset_1(k1_xboole_0, B_19, C_20)=k1_xboole_0 | ~v1_funct_2(C_20, k1_xboole_0, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.03/1.46  tff(c_261, plain, (![B_68, C_69]: (k1_relset_1('#skF_3', B_68, C_69)='#skF_3' | ~v1_funct_2(C_69, '#skF_3', B_68) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_68))))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_216, c_216, c_30])).
% 3.03/1.46  tff(c_264, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_261])).
% 3.03/1.46  tff(c_267, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_81, c_264])).
% 3.03/1.46  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_267])).
% 3.03/1.46  tff(c_271, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 3.03/1.46  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.03/1.46  tff(c_274, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_44])).
% 3.03/1.46  tff(c_294, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.03/1.46  tff(c_298, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_294])).
% 3.03/1.46  tff(c_455, plain, (![B_105, A_106, C_107]: (k1_xboole_0=B_105 | k1_relset_1(A_106, B_105, C_107)=A_106 | ~v1_funct_2(C_107, A_106, B_105) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.03/1.46  tff(c_458, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_455])).
% 3.03/1.46  tff(c_461, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_298, c_458])).
% 3.03/1.46  tff(c_462, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_461])).
% 3.03/1.46  tff(c_270, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 3.03/1.46  tff(c_277, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.03/1.46  tff(c_280, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_277])).
% 3.03/1.46  tff(c_283, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_280])).
% 3.03/1.46  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.03/1.46  tff(c_276, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_46])).
% 3.03/1.46  tff(c_368, plain, (![B_95, A_96, C_97]: (k1_xboole_0=B_95 | k1_relset_1(A_96, B_95, C_97)=A_96 | ~v1_funct_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.03/1.46  tff(c_371, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_368])).
% 3.03/1.46  tff(c_374, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_298, c_371])).
% 3.03/1.46  tff(c_375, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_374])).
% 3.03/1.46  tff(c_42, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.03/1.46  tff(c_285, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_42])).
% 3.03/1.46  tff(c_323, plain, (![B_91, A_92]: (k1_funct_1(k2_funct_1(B_91), k1_funct_1(B_91, A_92))=A_92 | ~r2_hidden(A_92, k1_relat_1(B_91)) | ~v2_funct_1(B_91) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.03/1.46  tff(c_341, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_285, c_323])).
% 3.03/1.46  tff(c_345, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | ~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_38, c_271, c_341])).
% 3.03/1.46  tff(c_346, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_345])).
% 3.03/1.46  tff(c_376, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_346])).
% 3.03/1.46  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_276, c_376])).
% 3.03/1.46  tff(c_382, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_374])).
% 3.03/1.46  tff(c_381, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_374])).
% 3.03/1.46  tff(c_403, plain, (![B_101, C_102]: (k1_relset_1('#skF_3', B_101, C_102)='#skF_3' | ~v1_funct_2(C_102, '#skF_3', B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_101))))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_381, c_381, c_381, c_30])).
% 3.03/1.46  tff(c_406, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_403])).
% 3.03/1.46  tff(c_409, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_298, c_406])).
% 3.03/1.46  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_409])).
% 3.03/1.46  tff(c_412, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_345])).
% 3.03/1.46  tff(c_18, plain, (![B_14, A_13]: (k1_funct_1(k2_funct_1(B_14), k1_funct_1(B_14, A_13))=A_13 | ~r2_hidden(A_13, k1_relat_1(B_14)) | ~v2_funct_1(B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.03/1.46  tff(c_421, plain, ('#skF_5'='#skF_6' | ~r2_hidden('#skF_6', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_412, c_18])).
% 3.03/1.46  tff(c_428, plain, ('#skF_5'='#skF_6' | ~r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_38, c_271, c_421])).
% 3.03/1.46  tff(c_429, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_270, c_428])).
% 3.03/1.46  tff(c_463, plain, (~r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_429])).
% 3.03/1.46  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_463])).
% 3.03/1.46  tff(c_470, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_461])).
% 3.03/1.46  tff(c_469, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_461])).
% 3.03/1.46  tff(c_547, plain, (![B_117, C_118]: (k1_relset_1('#skF_3', B_117, C_118)='#skF_3' | ~v1_funct_2(C_118, '#skF_3', B_117) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_117))))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_469, c_469, c_469, c_30])).
% 3.03/1.46  tff(c_550, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_547])).
% 3.03/1.46  tff(c_553, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_298, c_550])).
% 3.03/1.46  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_470, c_553])).
% 3.03/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.46  
% 3.03/1.46  Inference rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Ref     : 5
% 3.03/1.46  #Sup     : 98
% 3.03/1.46  #Fact    : 0
% 3.03/1.46  #Define  : 0
% 3.03/1.46  #Split   : 6
% 3.03/1.46  #Chain   : 0
% 3.03/1.46  #Close   : 0
% 3.03/1.46  
% 3.03/1.46  Ordering : KBO
% 3.03/1.46  
% 3.03/1.46  Simplification rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Subsume      : 12
% 3.03/1.46  #Demod        : 135
% 3.03/1.46  #Tautology    : 59
% 3.03/1.46  #SimpNegUnit  : 11
% 3.03/1.46  #BackRed      : 24
% 3.03/1.46  
% 3.03/1.46  #Partial instantiations: 0
% 3.03/1.46  #Strategies tried      : 1
% 3.03/1.46  
% 3.03/1.46  Timing (in seconds)
% 3.03/1.46  ----------------------
% 3.03/1.47  Preprocessing        : 0.34
% 3.03/1.47  Parsing              : 0.18
% 3.03/1.47  CNF conversion       : 0.02
% 3.03/1.47  Main loop            : 0.32
% 3.03/1.47  Inferencing          : 0.11
% 3.03/1.47  Reduction            : 0.10
% 3.03/1.47  Demodulation         : 0.07
% 3.03/1.47  BG Simplification    : 0.03
% 3.03/1.47  Subsumption          : 0.06
% 3.03/1.47  Abstraction          : 0.02
% 3.03/1.47  MUC search           : 0.00
% 3.03/1.47  Cooper               : 0.00
% 3.03/1.47  Total                : 0.70
% 3.03/1.47  Index Insertion      : 0.00
% 3.03/1.47  Index Deletion       : 0.00
% 3.03/1.47  Index Matching       : 0.00
% 3.03/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
