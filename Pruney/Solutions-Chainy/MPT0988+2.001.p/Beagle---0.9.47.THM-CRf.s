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
% DateTime   : Thu Dec  3 10:12:54 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  141 (3464 expanded)
%              Number of leaves         :   32 (1300 expanded)
%              Depth                    :   19
%              Number of atoms          :  437 (23034 expanded)
%              Number of equality atoms :  185 (9763 expanded)
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

tff(f_128,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
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

tff(f_57,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_81,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_81])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_88,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_81])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_142,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_148,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_142])).

tff(c_151,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_148])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_124,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_131,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_124])).

tff(c_177,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_180,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_6','#skF_5','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_177])).

tff(c_186,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_131,c_180])).

tff(c_187,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_186])).

tff(c_418,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_421,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_151,c_418])).

tff(c_423,plain,(
    ! [B_81] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_81)) = '#skF_1'('#skF_7',B_81)
      | r2_hidden('#skF_3'('#skF_7',B_81),'#skF_6')
      | k2_funct_1('#skF_7') = B_81
      | k1_relat_1(B_81) != '#skF_6'
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_151,c_421])).

tff(c_437,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_72,plain,(
    ! [E_37] :
      ( r2_hidden(k1_funct_1('#skF_8',E_37),'#skF_5')
      | ~ r2_hidden(E_37,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_510,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_437,c_72])).

tff(c_620,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_4'(A_88,'#skF_8'),'#skF_5')
      | ~ r2_hidden('#skF_3'(A_88,'#skF_8'),'#skF_6')
      | k1_funct_1(A_88,'#skF_2'(A_88,'#skF_8')) = '#skF_1'(A_88,'#skF_8')
      | k2_funct_1(A_88) = '#skF_8'
      | k2_relat_1(A_88) != '#skF_6'
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_187,c_510])).

tff(c_623,plain,
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
    inference(resolution,[status(thm)],[c_423,c_620])).

tff(c_629,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_187,c_89,c_68,c_54,c_151,c_623])).

tff(c_630,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_629])).

tff(c_635,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_630])).

tff(c_76,plain,(
    ! [F_38] :
      ( r2_hidden(k1_funct_1('#skF_7',F_38),'#skF_6')
      | ~ r2_hidden(F_38,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_652,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_76])).

tff(c_671,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_132,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_124])).

tff(c_183,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_177])).

tff(c_190,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_132,c_183])).

tff(c_191,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_190])).

tff(c_326,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_329,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_151,c_326])).

tff(c_331,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_2'('#skF_7',B_75),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_75),'#skF_6')
      | k2_funct_1('#skF_7') = B_75
      | k1_relat_1(B_75) != '#skF_6'
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_151,c_191,c_329])).

tff(c_333,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_364,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_191,c_333])).

tff(c_371,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_2'('#skF_7',B_78),'#skF_5')
      | k1_funct_1(B_78,'#skF_3'('#skF_7',B_78)) = '#skF_4'('#skF_7',B_78)
      | k2_funct_1('#skF_7') = B_78
      | k1_relat_1(B_78) != '#skF_6'
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_151,c_364])).

tff(c_674,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_371,c_671])).

tff(c_677,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_187,c_674])).

tff(c_678,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_677])).

tff(c_695,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_72])).

tff(c_707,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_695])).

tff(c_713,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_331,c_707])).

tff(c_720,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_187,c_713])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_671,c_720])).

tff(c_723,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_695])).

tff(c_724,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_695])).

tff(c_70,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8',E_37)) = E_37
      | ~ r2_hidden(E_37,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_692,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_70])).

tff(c_743,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_692])).

tff(c_731,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_2'(A_91,B_92),k1_relat_1(A_91))
      | k1_funct_1(A_91,'#skF_4'(A_91,B_92)) != '#skF_3'(A_91,B_92)
      | ~ r2_hidden('#skF_4'(A_91,B_92),k1_relat_1(A_91))
      | k2_funct_1(A_91) = B_92
      | k2_relat_1(A_91) != k1_relat_1(B_92)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_734,plain,(
    ! [B_92] :
      ( r2_hidden('#skF_2'('#skF_7',B_92),'#skF_5')
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_92)) != '#skF_3'('#skF_7',B_92)
      | ~ r2_hidden('#skF_4'('#skF_7',B_92),k1_relat_1('#skF_7'))
      | k2_funct_1('#skF_7') = B_92
      | k2_relat_1('#skF_7') != k1_relat_1(B_92)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_731])).

tff(c_770,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_2'('#skF_7',B_93),'#skF_5')
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_93)) != '#skF_3'('#skF_7',B_93)
      | ~ r2_hidden('#skF_4'('#skF_7',B_93),'#skF_5')
      | k2_funct_1('#skF_7') = B_93
      | k1_relat_1(B_93) != '#skF_6'
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_151,c_191,c_734])).

tff(c_773,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_770,c_671])).

tff(c_776,plain,(
    k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_187,c_723,c_743,c_773])).

tff(c_778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_776])).

tff(c_779,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_780,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_74,plain,(
    ! [F_38] :
      ( k1_funct_1('#skF_8',k1_funct_1('#skF_7',F_38)) = F_38
      | ~ r2_hidden(F_38,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_649,plain,
    ( k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) = '#skF_2'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_74])).

tff(c_781,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_649])).

tff(c_783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_781])).

tff(c_784,plain,(
    k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) = '#skF_2'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_649])).

tff(c_14,plain,(
    ! [B_11,A_1] :
      ( k1_funct_1(B_11,'#skF_1'(A_1,B_11)) != '#skF_2'(A_1,B_11)
      | ~ r2_hidden('#skF_1'(A_1,B_11),k2_relat_1(A_1))
      | r2_hidden('#skF_3'(A_1,B_11),k2_relat_1(A_1))
      | k2_funct_1(A_1) = B_11
      | k2_relat_1(A_1) != k1_relat_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_800,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | r2_hidden('#skF_3'('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | k2_funct_1('#skF_7') = '#skF_8'
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_14])).

tff(c_817,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_88,c_62,c_151,c_187,c_151,c_779,c_151,c_800])).

tff(c_818,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_817])).

tff(c_969,plain,(
    ! [B_100,A_101] :
      ( k1_funct_1(B_100,'#skF_1'(A_101,B_100)) != '#skF_2'(A_101,B_100)
      | ~ r2_hidden('#skF_1'(A_101,B_100),k2_relat_1(A_101))
      | k1_funct_1(B_100,'#skF_3'(A_101,B_100)) = '#skF_4'(A_101,B_100)
      | k2_funct_1(A_101) = B_100
      | k2_relat_1(A_101) != k1_relat_1(B_100)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_971,plain,(
    ! [B_100] :
      ( k1_funct_1(B_100,'#skF_1'('#skF_7',B_100)) != '#skF_2'('#skF_7',B_100)
      | ~ r2_hidden('#skF_1'('#skF_7',B_100),'#skF_6')
      | k1_funct_1(B_100,'#skF_3'('#skF_7',B_100)) = '#skF_4'('#skF_7',B_100)
      | k2_funct_1('#skF_7') = B_100
      | k2_relat_1('#skF_7') != k1_relat_1(B_100)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_969])).

tff(c_974,plain,(
    ! [B_102] :
      ( k1_funct_1(B_102,'#skF_1'('#skF_7',B_102)) != '#skF_2'('#skF_7',B_102)
      | ~ r2_hidden('#skF_1'('#skF_7',B_102),'#skF_6')
      | k1_funct_1(B_102,'#skF_3'('#skF_7',B_102)) = '#skF_4'('#skF_7',B_102)
      | k2_funct_1('#skF_7') = B_102
      | k1_relat_1(B_102) != '#skF_6'
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_151,c_971])).

tff(c_976,plain,
    ( k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) != '#skF_2'('#skF_7','#skF_8')
    | k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_779,c_974])).

tff(c_981,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_187,c_784,c_976])).

tff(c_982,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_981])).

tff(c_1003,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_72])).

tff(c_1024,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_1003])).

tff(c_1000,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_70])).

tff(c_1022,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_1000])).

tff(c_1428,plain,(
    ! [B_116,A_117] :
      ( k1_funct_1(B_116,'#skF_1'(A_117,B_116)) != '#skF_2'(A_117,B_116)
      | ~ r2_hidden('#skF_1'(A_117,B_116),k2_relat_1(A_117))
      | k1_funct_1(A_117,'#skF_4'(A_117,B_116)) != '#skF_3'(A_117,B_116)
      | ~ r2_hidden('#skF_4'(A_117,B_116),k1_relat_1(A_117))
      | k2_funct_1(A_117) = B_116
      | k2_relat_1(A_117) != k1_relat_1(B_116)
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1431,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_784,c_1428])).

tff(c_1434,plain,(
    k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_88,c_62,c_151,c_187,c_1024,c_191,c_1022,c_779,c_151,c_1431])).

tff(c_1436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1434])).

tff(c_1438,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) != '#skF_1'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_630])).

tff(c_10,plain,(
    ! [A_1,B_11] :
      ( k1_funct_1(A_1,'#skF_2'(A_1,B_11)) = '#skF_1'(A_1,B_11)
      | k1_funct_1(B_11,'#skF_3'(A_1,B_11)) = '#skF_4'(A_1,B_11)
      | k2_funct_1(A_1) = B_11
      | k2_relat_1(A_1) != k1_relat_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1441,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1438])).

tff(c_1444,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_88,c_62,c_151,c_187,c_1441])).

tff(c_1445,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1444])).

tff(c_1459,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1445,c_70])).

tff(c_1475,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1459])).

tff(c_1478,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_423,c_1475])).

tff(c_1484,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_187,c_1478])).

tff(c_1486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1438,c_1484])).

tff(c_1487,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1459])).

tff(c_1437,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_630])).

tff(c_1964,plain,(
    ! [A_134,B_135] :
      ( k1_funct_1(A_134,'#skF_2'(A_134,B_135)) = '#skF_1'(A_134,B_135)
      | k1_funct_1(A_134,'#skF_4'(A_134,B_135)) != '#skF_3'(A_134,B_135)
      | ~ r2_hidden('#skF_4'(A_134,B_135),k1_relat_1(A_134))
      | k2_funct_1(A_134) = B_135
      | k2_relat_1(A_134) != k1_relat_1(B_135)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135)
      | ~ v2_funct_1(A_134)
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1967,plain,(
    ! [B_135] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_135)) = '#skF_1'('#skF_7',B_135)
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_135)) != '#skF_3'('#skF_7',B_135)
      | ~ r2_hidden('#skF_4'('#skF_7',B_135),'#skF_5')
      | k2_funct_1('#skF_7') = B_135
      | k2_relat_1('#skF_7') != k1_relat_1(B_135)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_1964])).

tff(c_1975,plain,(
    ! [B_136] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_136)) = '#skF_1'('#skF_7',B_136)
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_136)) != '#skF_3'('#skF_7',B_136)
      | ~ r2_hidden('#skF_4'('#skF_7',B_136),'#skF_5')
      | k2_funct_1('#skF_7') = B_136
      | k1_relat_1(B_136) != '#skF_6'
      | ~ v1_funct_1(B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_68,c_54,c_151,c_1967])).

tff(c_1978,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1437,c_1975])).

tff(c_1981,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_187,c_1487,c_1978])).

tff(c_1983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1438,c_1981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:35:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.80  
% 4.73/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.80  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.73/1.80  
% 4.73/1.80  %Foreground sorts:
% 4.73/1.80  
% 4.73/1.80  
% 4.73/1.80  %Background operators:
% 4.73/1.80  
% 4.73/1.80  
% 4.73/1.80  %Foreground operators:
% 4.73/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.73/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.73/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.73/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.73/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.73/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.73/1.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.73/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.73/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.73/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.73/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.73/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.73/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.73/1.80  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.73/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.73/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.73/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.73/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.73/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.73/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.73/1.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.73/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.73/1.80  
% 4.90/1.82  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) & (![E, F]: (((r2_hidden(E, B) & (k1_funct_1(D, E) = F)) => (r2_hidden(F, A) & (k1_funct_1(C, F) = E))) & ((r2_hidden(F, A) & (k1_funct_1(C, F) = E)) => (r2_hidden(E, B) & (k1_funct_1(D, E) = F)))))) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_2)).
% 4.90/1.82  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.90/1.82  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.90/1.82  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.90/1.82  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.90/1.82  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 4.90/1.82  tff(c_48, plain, (k2_funct_1('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_81, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.90/1.82  tff(c_89, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_81])).
% 4.90/1.82  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_54, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_88, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_81])).
% 4.90/1.82  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_56, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_142, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.90/1.82  tff(c_148, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_142])).
% 4.90/1.82  tff(c_151, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_148])).
% 4.90/1.82  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_124, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.90/1.82  tff(c_131, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_124])).
% 4.90/1.82  tff(c_177, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.90/1.82  tff(c_180, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_6', '#skF_5', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_177])).
% 4.90/1.82  tff(c_186, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_131, c_180])).
% 4.90/1.82  tff(c_187, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52, c_186])).
% 4.90/1.82  tff(c_418, plain, (![A_80, B_81]: (k1_funct_1(A_80, '#skF_2'(A_80, B_81))='#skF_1'(A_80, B_81) | r2_hidden('#skF_3'(A_80, B_81), k2_relat_1(A_80)) | k2_funct_1(A_80)=B_81 | k2_relat_1(A_80)!=k1_relat_1(B_81) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81) | ~v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_421, plain, (![B_81]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_81))='#skF_1'('#skF_7', B_81) | r2_hidden('#skF_3'('#skF_7', B_81), '#skF_6') | k2_funct_1('#skF_7')=B_81 | k2_relat_1('#skF_7')!=k1_relat_1(B_81) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_418])).
% 4.90/1.82  tff(c_423, plain, (![B_81]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_81))='#skF_1'('#skF_7', B_81) | r2_hidden('#skF_3'('#skF_7', B_81), '#skF_6') | k2_funct_1('#skF_7')=B_81 | k1_relat_1(B_81)!='#skF_6' | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_151, c_421])).
% 4.90/1.82  tff(c_437, plain, (![A_84, B_85]: (k1_funct_1(A_84, '#skF_2'(A_84, B_85))='#skF_1'(A_84, B_85) | k1_funct_1(B_85, '#skF_3'(A_84, B_85))='#skF_4'(A_84, B_85) | k2_funct_1(A_84)=B_85 | k2_relat_1(A_84)!=k1_relat_1(B_85) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85) | ~v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_72, plain, (![E_37]: (r2_hidden(k1_funct_1('#skF_8', E_37), '#skF_5') | ~r2_hidden(E_37, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_510, plain, (![A_84]: (r2_hidden('#skF_4'(A_84, '#skF_8'), '#skF_5') | ~r2_hidden('#skF_3'(A_84, '#skF_8'), '#skF_6') | k1_funct_1(A_84, '#skF_2'(A_84, '#skF_8'))='#skF_1'(A_84, '#skF_8') | k2_funct_1(A_84)='#skF_8' | k2_relat_1(A_84)!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_437, c_72])).
% 4.90/1.82  tff(c_620, plain, (![A_88]: (r2_hidden('#skF_4'(A_88, '#skF_8'), '#skF_5') | ~r2_hidden('#skF_3'(A_88, '#skF_8'), '#skF_6') | k1_funct_1(A_88, '#skF_2'(A_88, '#skF_8'))='#skF_1'(A_88, '#skF_8') | k2_funct_1(A_88)='#skF_8' | k2_relat_1(A_88)!='#skF_6' | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_187, c_510])).
% 4.90/1.82  tff(c_623, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k2_relat_1('#skF_7')!='#skF_6' | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_423, c_620])).
% 4.90/1.82  tff(c_629, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_187, c_89, c_68, c_54, c_151, c_623])).
% 4.90/1.82  tff(c_630, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_48, c_629])).
% 4.90/1.82  tff(c_635, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_630])).
% 4.90/1.82  tff(c_76, plain, (![F_38]: (r2_hidden(k1_funct_1('#skF_7', F_38), '#skF_6') | ~r2_hidden(F_38, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_652, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_8'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_635, c_76])).
% 4.90/1.82  tff(c_671, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_652])).
% 4.90/1.82  tff(c_50, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_66, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_132, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_124])).
% 4.90/1.82  tff(c_183, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_177])).
% 4.90/1.82  tff(c_190, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_132, c_183])).
% 4.90/1.82  tff(c_191, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_50, c_190])).
% 4.90/1.82  tff(c_326, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), k1_relat_1(A_74)) | r2_hidden('#skF_3'(A_74, B_75), k2_relat_1(A_74)) | k2_funct_1(A_74)=B_75 | k2_relat_1(A_74)!=k1_relat_1(B_75) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_329, plain, (![B_75]: (r2_hidden('#skF_2'('#skF_7', B_75), k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_7', B_75), '#skF_6') | k2_funct_1('#skF_7')=B_75 | k2_relat_1('#skF_7')!=k1_relat_1(B_75) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_326])).
% 4.90/1.82  tff(c_331, plain, (![B_75]: (r2_hidden('#skF_2'('#skF_7', B_75), '#skF_5') | r2_hidden('#skF_3'('#skF_7', B_75), '#skF_6') | k2_funct_1('#skF_7')=B_75 | k1_relat_1(B_75)!='#skF_6' | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_151, c_191, c_329])).
% 4.90/1.82  tff(c_333, plain, (![A_77, B_78]: (r2_hidden('#skF_2'(A_77, B_78), k1_relat_1(A_77)) | k1_funct_1(B_78, '#skF_3'(A_77, B_78))='#skF_4'(A_77, B_78) | k2_funct_1(A_77)=B_78 | k2_relat_1(A_77)!=k1_relat_1(B_78) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_364, plain, (![B_78]: (r2_hidden('#skF_2'('#skF_7', B_78), '#skF_5') | k1_funct_1(B_78, '#skF_3'('#skF_7', B_78))='#skF_4'('#skF_7', B_78) | k2_funct_1('#skF_7')=B_78 | k2_relat_1('#skF_7')!=k1_relat_1(B_78) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_333])).
% 4.90/1.82  tff(c_371, plain, (![B_78]: (r2_hidden('#skF_2'('#skF_7', B_78), '#skF_5') | k1_funct_1(B_78, '#skF_3'('#skF_7', B_78))='#skF_4'('#skF_7', B_78) | k2_funct_1('#skF_7')=B_78 | k1_relat_1(B_78)!='#skF_6' | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_151, c_364])).
% 4.90/1.82  tff(c_674, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_371, c_671])).
% 4.90/1.82  tff(c_677, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_187, c_674])).
% 4.90/1.82  tff(c_678, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_48, c_677])).
% 4.90/1.82  tff(c_695, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_678, c_72])).
% 4.90/1.82  tff(c_707, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_695])).
% 4.90/1.82  tff(c_713, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_331, c_707])).
% 4.90/1.82  tff(c_720, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_187, c_713])).
% 4.90/1.82  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_671, c_720])).
% 4.90/1.82  tff(c_723, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_695])).
% 4.90/1.82  tff(c_724, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_695])).
% 4.90/1.82  tff(c_70, plain, (![E_37]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', E_37))=E_37 | ~r2_hidden(E_37, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_692, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_678, c_70])).
% 4.90/1.82  tff(c_743, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_724, c_692])).
% 4.90/1.82  tff(c_731, plain, (![A_91, B_92]: (r2_hidden('#skF_2'(A_91, B_92), k1_relat_1(A_91)) | k1_funct_1(A_91, '#skF_4'(A_91, B_92))!='#skF_3'(A_91, B_92) | ~r2_hidden('#skF_4'(A_91, B_92), k1_relat_1(A_91)) | k2_funct_1(A_91)=B_92 | k2_relat_1(A_91)!=k1_relat_1(B_92) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_734, plain, (![B_92]: (r2_hidden('#skF_2'('#skF_7', B_92), '#skF_5') | k1_funct_1('#skF_7', '#skF_4'('#skF_7', B_92))!='#skF_3'('#skF_7', B_92) | ~r2_hidden('#skF_4'('#skF_7', B_92), k1_relat_1('#skF_7')) | k2_funct_1('#skF_7')=B_92 | k2_relat_1('#skF_7')!=k1_relat_1(B_92) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_731])).
% 4.90/1.82  tff(c_770, plain, (![B_93]: (r2_hidden('#skF_2'('#skF_7', B_93), '#skF_5') | k1_funct_1('#skF_7', '#skF_4'('#skF_7', B_93))!='#skF_3'('#skF_7', B_93) | ~r2_hidden('#skF_4'('#skF_7', B_93), '#skF_5') | k2_funct_1('#skF_7')=B_93 | k1_relat_1(B_93)!='#skF_6' | ~v1_funct_1(B_93) | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_151, c_191, c_734])).
% 4.90/1.82  tff(c_773, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))!='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_770, c_671])).
% 4.90/1.82  tff(c_776, plain, (k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_187, c_723, c_743, c_773])).
% 4.90/1.82  tff(c_778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_776])).
% 4.90/1.82  tff(c_779, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_652])).
% 4.90/1.82  tff(c_780, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_652])).
% 4.90/1.82  tff(c_74, plain, (![F_38]: (k1_funct_1('#skF_8', k1_funct_1('#skF_7', F_38))=F_38 | ~r2_hidden(F_38, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.90/1.82  tff(c_649, plain, (k1_funct_1('#skF_8', '#skF_1'('#skF_7', '#skF_8'))='#skF_2'('#skF_7', '#skF_8') | ~r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_635, c_74])).
% 4.90/1.82  tff(c_781, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_649])).
% 4.90/1.82  tff(c_783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_780, c_781])).
% 4.90/1.82  tff(c_784, plain, (k1_funct_1('#skF_8', '#skF_1'('#skF_7', '#skF_8'))='#skF_2'('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_649])).
% 4.90/1.82  tff(c_14, plain, (![B_11, A_1]: (k1_funct_1(B_11, '#skF_1'(A_1, B_11))!='#skF_2'(A_1, B_11) | ~r2_hidden('#skF_1'(A_1, B_11), k2_relat_1(A_1)) | r2_hidden('#skF_3'(A_1, B_11), k2_relat_1(A_1)) | k2_funct_1(A_1)=B_11 | k2_relat_1(A_1)!=k1_relat_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_800, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_8'), k2_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_7', '#skF_8'), k2_relat_1('#skF_7')) | k2_funct_1('#skF_7')='#skF_8' | k2_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_784, c_14])).
% 4.90/1.82  tff(c_817, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_88, c_62, c_151, c_187, c_151, c_779, c_151, c_800])).
% 4.90/1.82  tff(c_818, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_817])).
% 4.90/1.82  tff(c_969, plain, (![B_100, A_101]: (k1_funct_1(B_100, '#skF_1'(A_101, B_100))!='#skF_2'(A_101, B_100) | ~r2_hidden('#skF_1'(A_101, B_100), k2_relat_1(A_101)) | k1_funct_1(B_100, '#skF_3'(A_101, B_100))='#skF_4'(A_101, B_100) | k2_funct_1(A_101)=B_100 | k2_relat_1(A_101)!=k1_relat_1(B_100) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_971, plain, (![B_100]: (k1_funct_1(B_100, '#skF_1'('#skF_7', B_100))!='#skF_2'('#skF_7', B_100) | ~r2_hidden('#skF_1'('#skF_7', B_100), '#skF_6') | k1_funct_1(B_100, '#skF_3'('#skF_7', B_100))='#skF_4'('#skF_7', B_100) | k2_funct_1('#skF_7')=B_100 | k2_relat_1('#skF_7')!=k1_relat_1(B_100) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_969])).
% 4.90/1.82  tff(c_974, plain, (![B_102]: (k1_funct_1(B_102, '#skF_1'('#skF_7', B_102))!='#skF_2'('#skF_7', B_102) | ~r2_hidden('#skF_1'('#skF_7', B_102), '#skF_6') | k1_funct_1(B_102, '#skF_3'('#skF_7', B_102))='#skF_4'('#skF_7', B_102) | k2_funct_1('#skF_7')=B_102 | k1_relat_1(B_102)!='#skF_6' | ~v1_funct_1(B_102) | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_151, c_971])).
% 4.90/1.82  tff(c_976, plain, (k1_funct_1('#skF_8', '#skF_1'('#skF_7', '#skF_8'))!='#skF_2'('#skF_7', '#skF_8') | k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_779, c_974])).
% 4.90/1.82  tff(c_981, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_187, c_784, c_976])).
% 4.90/1.82  tff(c_982, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_48, c_981])).
% 4.90/1.82  tff(c_1003, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_982, c_72])).
% 4.90/1.82  tff(c_1024, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_1003])).
% 4.90/1.82  tff(c_1000, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_982, c_70])).
% 4.90/1.82  tff(c_1022, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_1000])).
% 4.90/1.82  tff(c_1428, plain, (![B_116, A_117]: (k1_funct_1(B_116, '#skF_1'(A_117, B_116))!='#skF_2'(A_117, B_116) | ~r2_hidden('#skF_1'(A_117, B_116), k2_relat_1(A_117)) | k1_funct_1(A_117, '#skF_4'(A_117, B_116))!='#skF_3'(A_117, B_116) | ~r2_hidden('#skF_4'(A_117, B_116), k1_relat_1(A_117)) | k2_funct_1(A_117)=B_116 | k2_relat_1(A_117)!=k1_relat_1(B_116) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_1431, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_8'), k2_relat_1('#skF_7')) | k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))!='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_4'('#skF_7', '#skF_8'), k1_relat_1('#skF_7')) | k2_funct_1('#skF_7')='#skF_8' | k2_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_784, c_1428])).
% 4.90/1.82  tff(c_1434, plain, (k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_88, c_62, c_151, c_187, c_1024, c_191, c_1022, c_779, c_151, c_1431])).
% 4.90/1.82  tff(c_1436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1434])).
% 4.90/1.82  tff(c_1438, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))!='#skF_1'('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_630])).
% 4.90/1.82  tff(c_10, plain, (![A_1, B_11]: (k1_funct_1(A_1, '#skF_2'(A_1, B_11))='#skF_1'(A_1, B_11) | k1_funct_1(B_11, '#skF_3'(A_1, B_11))='#skF_4'(A_1, B_11) | k2_funct_1(A_1)=B_11 | k2_relat_1(A_1)!=k1_relat_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_1441, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k2_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1438])).
% 4.90/1.82  tff(c_1444, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_88, c_62, c_151, c_187, c_1441])).
% 4.90/1.82  tff(c_1445, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_48, c_1444])).
% 4.90/1.82  tff(c_1459, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1445, c_70])).
% 4.90/1.82  tff(c_1475, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1459])).
% 4.90/1.82  tff(c_1478, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_423, c_1475])).
% 4.90/1.82  tff(c_1484, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_187, c_1478])).
% 4.90/1.82  tff(c_1486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1438, c_1484])).
% 4.90/1.82  tff(c_1487, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_1459])).
% 4.90/1.82  tff(c_1437, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_630])).
% 4.90/1.82  tff(c_1964, plain, (![A_134, B_135]: (k1_funct_1(A_134, '#skF_2'(A_134, B_135))='#skF_1'(A_134, B_135) | k1_funct_1(A_134, '#skF_4'(A_134, B_135))!='#skF_3'(A_134, B_135) | ~r2_hidden('#skF_4'(A_134, B_135), k1_relat_1(A_134)) | k2_funct_1(A_134)=B_135 | k2_relat_1(A_134)!=k1_relat_1(B_135) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135) | ~v2_funct_1(A_134) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.82  tff(c_1967, plain, (![B_135]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_135))='#skF_1'('#skF_7', B_135) | k1_funct_1('#skF_7', '#skF_4'('#skF_7', B_135))!='#skF_3'('#skF_7', B_135) | ~r2_hidden('#skF_4'('#skF_7', B_135), '#skF_5') | k2_funct_1('#skF_7')=B_135 | k2_relat_1('#skF_7')!=k1_relat_1(B_135) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_1964])).
% 4.90/1.82  tff(c_1975, plain, (![B_136]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_136))='#skF_1'('#skF_7', B_136) | k1_funct_1('#skF_7', '#skF_4'('#skF_7', B_136))!='#skF_3'('#skF_7', B_136) | ~r2_hidden('#skF_4'('#skF_7', B_136), '#skF_5') | k2_funct_1('#skF_7')=B_136 | k1_relat_1(B_136)!='#skF_6' | ~v1_funct_1(B_136) | ~v1_relat_1(B_136))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_68, c_54, c_151, c_1967])).
% 4.90/1.82  tff(c_1978, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))!='#skF_3'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1437, c_1975])).
% 4.90/1.82  tff(c_1981, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_187, c_1487, c_1978])).
% 4.90/1.82  tff(c_1983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1438, c_1981])).
% 4.90/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.82  
% 4.90/1.82  Inference rules
% 4.90/1.82  ----------------------
% 4.90/1.82  #Ref     : 0
% 4.90/1.82  #Sup     : 378
% 4.90/1.82  #Fact    : 0
% 4.90/1.82  #Define  : 0
% 4.90/1.82  #Split   : 9
% 4.90/1.82  #Chain   : 0
% 4.90/1.82  #Close   : 0
% 4.90/1.82  
% 4.90/1.82  Ordering : KBO
% 4.90/1.82  
% 4.90/1.82  Simplification rules
% 4.90/1.82  ----------------------
% 4.90/1.82  #Subsume      : 78
% 4.90/1.82  #Demod        : 778
% 4.90/1.82  #Tautology    : 206
% 4.90/1.82  #SimpNegUnit  : 57
% 4.90/1.82  #BackRed      : 2
% 4.90/1.82  
% 4.90/1.82  #Partial instantiations: 0
% 4.90/1.82  #Strategies tried      : 1
% 4.90/1.82  
% 4.90/1.82  Timing (in seconds)
% 4.90/1.82  ----------------------
% 4.90/1.83  Preprocessing        : 0.34
% 4.90/1.83  Parsing              : 0.17
% 4.90/1.83  CNF conversion       : 0.03
% 4.90/1.83  Main loop            : 0.71
% 4.90/1.83  Inferencing          : 0.25
% 4.90/1.83  Reduction            : 0.23
% 4.90/1.83  Demodulation         : 0.17
% 4.90/1.83  BG Simplification    : 0.04
% 4.90/1.83  Subsumption          : 0.15
% 4.90/1.83  Abstraction          : 0.04
% 4.90/1.83  MUC search           : 0.00
% 4.90/1.83  Cooper               : 0.00
% 4.90/1.83  Total                : 1.10
% 4.90/1.83  Index Insertion      : 0.00
% 4.90/1.83  Index Deletion       : 0.00
% 4.90/1.83  Index Matching       : 0.00
% 4.90/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
