%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0988+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:12 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  142 (3465 expanded)
%              Number of leaves         :   32 (1300 expanded)
%              Depth                    :   19
%              Number of atoms          :  441 (23038 expanded)
%              Number of equality atoms :  187 (9765 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & v2_funct_1(C)
                & ! [E,F] :
                    ( ( ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F )
                     => ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E ) )
                    & ( ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E )
                     => ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F ) ) ) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

tff(c_48,plain,(
    k2_funct_1('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_83,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_91,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_83])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_90,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_83])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_142,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_148,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_142])).

tff(c_151,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_148])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_124,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_124])).

tff(c_163,plain,(
    ! [B_59,A_60,C_61] :
      ( k1_xboole_0 = B_59
      | k1_relset_1(A_60,B_59,C_61) = A_60
      | ~ v1_funct_2(C_61,A_60,B_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_6','#skF_5','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_172,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_131,c_166])).

tff(c_173,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_172])).

tff(c_420,plain,(
    ! [A_80,B_81] :
      ( k1_funct_1(A_80,'#skF_2'(A_80,B_81)) = '#skF_1'(A_80,B_81)
      | r2_hidden('#skF_3'(A_80,B_81),k2_relat_1(A_80))
      | k2_funct_1(A_80) = B_81
      | k2_relat_1(A_80) != k1_relat_1(B_81)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_423,plain,(
    ! [B_81] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_81)) = '#skF_1'('#skF_7',B_81)
      | r2_hidden('#skF_3'('#skF_7',B_81),'#skF_6')
      | k2_funct_1('#skF_7') = B_81
      | k2_relat_1('#skF_7') != k1_relat_1(B_81)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_420])).

tff(c_425,plain,(
    ! [B_81] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_81)) = '#skF_1'('#skF_7',B_81)
      | r2_hidden('#skF_3'('#skF_7',B_81),'#skF_6')
      | k2_funct_1('#skF_7') = B_81
      | k1_relat_1(B_81) != '#skF_6'
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_151,c_423])).

tff(c_439,plain,(
    ! [A_84,B_85] :
      ( k1_funct_1(A_84,'#skF_2'(A_84,B_85)) = '#skF_1'(A_84,B_85)
      | k1_funct_1(B_85,'#skF_3'(A_84,B_85)) = '#skF_4'(A_84,B_85)
      | k2_funct_1(A_84) = B_85
      | k2_relat_1(A_84) != k1_relat_1(B_85)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85)
      | ~ v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_72,plain,(
    ! [E_37] :
      ( r2_hidden(k1_funct_1('#skF_8',E_37),'#skF_5')
      | ~ r2_hidden(E_37,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_512,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_4'(A_84,'#skF_8'),'#skF_5')
      | ~ r2_hidden('#skF_3'(A_84,'#skF_8'),'#skF_6')
      | k1_funct_1(A_84,'#skF_2'(A_84,'#skF_8')) = '#skF_1'(A_84,'#skF_8')
      | k2_funct_1(A_84) = '#skF_8'
      | k2_relat_1(A_84) != k1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_72])).

tff(c_622,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_4'(A_88,'#skF_8'),'#skF_5')
      | ~ r2_hidden('#skF_3'(A_88,'#skF_8'),'#skF_6')
      | k1_funct_1(A_88,'#skF_2'(A_88,'#skF_8')) = '#skF_1'(A_88,'#skF_8')
      | k2_funct_1(A_88) = '#skF_8'
      | k2_relat_1(A_88) != '#skF_6'
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_173,c_512])).

tff(c_625,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k2_relat_1('#skF_7') != '#skF_6'
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_425,c_622])).

tff(c_631,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_173,c_91,c_68,c_54,c_151,c_625])).

tff(c_632,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_631])).

tff(c_637,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_76,plain,(
    ! [F_38] :
      ( r2_hidden(k1_funct_1('#skF_7',F_38),'#skF_6')
      | ~ r2_hidden(F_38,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_664,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_76])).

tff(c_683,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_132,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_124])).

tff(c_169,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_163])).

tff(c_176,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_132,c_169])).

tff(c_177,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_176])).

tff(c_328,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),k1_relat_1(A_74))
      | r2_hidden('#skF_3'(A_74,B_75),k2_relat_1(A_74))
      | k2_funct_1(A_74) = B_75
      | k2_relat_1(A_74) != k1_relat_1(B_75)
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_331,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_2'('#skF_7',B_75),k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_7',B_75),'#skF_6')
      | k2_funct_1('#skF_7') = B_75
      | k2_relat_1('#skF_7') != k1_relat_1(B_75)
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_328])).

tff(c_333,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_2'('#skF_7',B_75),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_75),'#skF_6')
      | k2_funct_1('#skF_7') = B_75
      | k1_relat_1(B_75) != '#skF_6'
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_151,c_177,c_331])).

tff(c_335,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_2'(A_77,B_78),k1_relat_1(A_77))
      | k1_funct_1(B_78,'#skF_3'(A_77,B_78)) = '#skF_4'(A_77,B_78)
      | k2_funct_1(A_77) = B_78
      | k2_relat_1(A_77) != k1_relat_1(B_78)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78)
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_366,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_2'('#skF_7',B_78),'#skF_5')
      | k1_funct_1(B_78,'#skF_3'('#skF_7',B_78)) = '#skF_4'('#skF_7',B_78)
      | k2_funct_1('#skF_7') = B_78
      | k2_relat_1('#skF_7') != k1_relat_1(B_78)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_335])).

tff(c_373,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_2'('#skF_7',B_78),'#skF_5')
      | k1_funct_1(B_78,'#skF_3'('#skF_7',B_78)) = '#skF_4'('#skF_7',B_78)
      | k2_funct_1('#skF_7') = B_78
      | k1_relat_1(B_78) != '#skF_6'
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_151,c_366])).

tff(c_686,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_373,c_683])).

tff(c_689,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_173,c_686])).

tff(c_690,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_689])).

tff(c_707,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_72])).

tff(c_719,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_725,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_333,c_719])).

tff(c_732,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_173,c_725])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_683,c_732])).

tff(c_735,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_736,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_70,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8',E_37)) = E_37
      | ~ r2_hidden(E_37,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_704,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_70])).

tff(c_745,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_704])).

tff(c_638,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_2'(A_89,B_90),k1_relat_1(A_89))
      | k1_funct_1(A_89,'#skF_4'(A_89,B_90)) != '#skF_3'(A_89,B_90)
      | ~ r2_hidden('#skF_4'(A_89,B_90),k1_relat_1(A_89))
      | k2_funct_1(A_89) = B_90
      | k2_relat_1(A_89) != k1_relat_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v2_funct_1(A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_641,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_2'('#skF_7',B_90),'#skF_5')
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_90)) != '#skF_3'('#skF_7',B_90)
      | ~ r2_hidden('#skF_4'('#skF_7',B_90),k1_relat_1('#skF_7'))
      | k2_funct_1('#skF_7') = B_90
      | k2_relat_1('#skF_7') != k1_relat_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_638])).

tff(c_772,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_2'('#skF_7',B_93),'#skF_5')
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_93)) != '#skF_3'('#skF_7',B_93)
      | ~ r2_hidden('#skF_4'('#skF_7',B_93),'#skF_5')
      | k2_funct_1('#skF_7') = B_93
      | k1_relat_1(B_93) != '#skF_6'
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_151,c_177,c_641])).

tff(c_775,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_772,c_683])).

tff(c_778,plain,(
    k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_173,c_735,c_745,c_775])).

tff(c_780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_778])).

tff(c_781,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_782,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_74,plain,(
    ! [F_38] :
      ( k1_funct_1('#skF_8',k1_funct_1('#skF_7',F_38)) = F_38
      | ~ r2_hidden(F_38,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_661,plain,
    ( k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) = '#skF_2'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_74])).

tff(c_783,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_661])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_783])).

tff(c_786,plain,(
    k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) = '#skF_2'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_661])).

tff(c_32,plain,(
    ! [B_23,A_13] :
      ( k1_funct_1(B_23,'#skF_1'(A_13,B_23)) != '#skF_2'(A_13,B_23)
      | ~ r2_hidden('#skF_1'(A_13,B_23),k2_relat_1(A_13))
      | r2_hidden('#skF_3'(A_13,B_23),k2_relat_1(A_13))
      | k2_funct_1(A_13) = B_23
      | k2_relat_1(A_13) != k1_relat_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_792,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | r2_hidden('#skF_3'('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | k2_funct_1('#skF_7') = '#skF_8'
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_32])).

tff(c_809,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_90,c_62,c_151,c_173,c_151,c_781,c_151,c_792])).

tff(c_810,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_809])).

tff(c_1145,plain,(
    ! [B_107,A_108] :
      ( k1_funct_1(B_107,'#skF_1'(A_108,B_107)) != '#skF_2'(A_108,B_107)
      | ~ r2_hidden('#skF_1'(A_108,B_107),k2_relat_1(A_108))
      | k1_funct_1(B_107,'#skF_3'(A_108,B_107)) = '#skF_4'(A_108,B_107)
      | k2_funct_1(A_108) = B_107
      | k2_relat_1(A_108) != k1_relat_1(B_107)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v2_funct_1(A_108)
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1147,plain,(
    ! [B_107] :
      ( k1_funct_1(B_107,'#skF_1'('#skF_7',B_107)) != '#skF_2'('#skF_7',B_107)
      | ~ r2_hidden('#skF_1'('#skF_7',B_107),'#skF_6')
      | k1_funct_1(B_107,'#skF_3'('#skF_7',B_107)) = '#skF_4'('#skF_7',B_107)
      | k2_funct_1('#skF_7') = B_107
      | k2_relat_1('#skF_7') != k1_relat_1(B_107)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_1145])).

tff(c_1150,plain,(
    ! [B_109] :
      ( k1_funct_1(B_109,'#skF_1'('#skF_7',B_109)) != '#skF_2'('#skF_7',B_109)
      | ~ r2_hidden('#skF_1'('#skF_7',B_109),'#skF_6')
      | k1_funct_1(B_109,'#skF_3'('#skF_7',B_109)) = '#skF_4'('#skF_7',B_109)
      | k2_funct_1('#skF_7') = B_109
      | k1_relat_1(B_109) != '#skF_6'
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_151,c_1147])).

tff(c_1152,plain,
    ( k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) != '#skF_2'('#skF_7','#skF_8')
    | k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_781,c_1150])).

tff(c_1157,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_173,c_786,c_1152])).

tff(c_1158,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1157])).

tff(c_1188,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_72])).

tff(c_1210,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_1188])).

tff(c_1185,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_70])).

tff(c_1208,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_1185])).

tff(c_1160,plain,(
    ! [B_110,A_111] :
      ( k1_funct_1(B_110,'#skF_1'(A_111,B_110)) != '#skF_2'(A_111,B_110)
      | ~ r2_hidden('#skF_1'(A_111,B_110),k2_relat_1(A_111))
      | k1_funct_1(A_111,'#skF_4'(A_111,B_110)) != '#skF_3'(A_111,B_110)
      | ~ r2_hidden('#skF_4'(A_111,B_110),k1_relat_1(A_111))
      | k2_funct_1(A_111) = B_110
      | k2_relat_1(A_111) != k1_relat_1(B_110)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1163,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),k1_relat_1('#skF_7'))
    | k2_funct_1('#skF_7') = '#skF_8'
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_1160])).

tff(c_1166,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_90,c_62,c_151,c_173,c_177,c_781,c_151,c_1163])).

tff(c_1167,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1166])).

tff(c_1248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_1208,c_1167])).

tff(c_1250,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) != '#skF_1'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_28,plain,(
    ! [A_13,B_23] :
      ( k1_funct_1(A_13,'#skF_2'(A_13,B_23)) = '#skF_1'(A_13,B_23)
      | k1_funct_1(B_23,'#skF_3'(A_13,B_23)) = '#skF_4'(A_13,B_23)
      | k2_funct_1(A_13) = B_23
      | k2_relat_1(A_13) != k1_relat_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1253,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1250])).

tff(c_1256,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_90,c_62,c_151,c_173,c_1253])).

tff(c_1257,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1256])).

tff(c_1271,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_70])).

tff(c_1287,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1271])).

tff(c_1290,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_425,c_1287])).

tff(c_1296,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_173,c_1290])).

tff(c_1298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1250,c_1296])).

tff(c_1299,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1271])).

tff(c_1249,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_1646,plain,(
    ! [A_124,B_125] :
      ( k1_funct_1(A_124,'#skF_2'(A_124,B_125)) = '#skF_1'(A_124,B_125)
      | k1_funct_1(A_124,'#skF_4'(A_124,B_125)) != '#skF_3'(A_124,B_125)
      | ~ r2_hidden('#skF_4'(A_124,B_125),k1_relat_1(A_124))
      | k2_funct_1(A_124) = B_125
      | k2_relat_1(A_124) != k1_relat_1(B_125)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1649,plain,(
    ! [B_125] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_125)) = '#skF_1'('#skF_7',B_125)
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_125)) != '#skF_3'('#skF_7',B_125)
      | ~ r2_hidden('#skF_4'('#skF_7',B_125),'#skF_5')
      | k2_funct_1('#skF_7') = B_125
      | k2_relat_1('#skF_7') != k1_relat_1(B_125)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_1646])).

tff(c_1657,plain,(
    ! [B_126] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_126)) = '#skF_1'('#skF_7',B_126)
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_126)) != '#skF_3'('#skF_7',B_126)
      | ~ r2_hidden('#skF_4'('#skF_7',B_126),'#skF_5')
      | k2_funct_1('#skF_7') = B_126
      | k1_relat_1(B_126) != '#skF_6'
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_54,c_151,c_1649])).

tff(c_1660,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1249,c_1657])).

tff(c_1663,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_173,c_1299,c_1660])).

tff(c_1665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1250,c_1663])).

%------------------------------------------------------------------------------
