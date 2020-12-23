%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:54 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 572 expanded)
%              Number of leaves         :   27 ( 192 expanded)
%              Depth                    :   13
%              Number of atoms          :  286 (2170 expanded)
%              Number of equality atoms :  107 ( 957 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v2_funct_1(C)
          <=> ! [D,E] :
                ( ( r2_hidden(D,A)
                  & r2_hidden(E,A)
                  & k1_funct_1(C,D) = k1_funct_1(C,E) )
               => D = E ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
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

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_57,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62,plain,(
    ! [A_26] :
      ( '#skF_2'(A_26) != '#skF_1'(A_26)
      | v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_65,plain,
    ( '#skF_2'('#skF_5') != '#skF_1'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_55])).

tff(c_68,plain,(
    '#skF_2'('#skF_5') != '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34,c_65])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_71,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_111,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_111])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75,c_114])).

tff(c_118,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_117])).

tff(c_10,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_126,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_10])).

tff(c_133,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34,c_126])).

tff(c_134,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_133])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_123,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_8])).

tff(c_130,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34,c_123])).

tff(c_131,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_130])).

tff(c_87,plain,(
    ! [A_35] :
      ( k1_funct_1(A_35,'#skF_2'(A_35)) = k1_funct_1(A_35,'#skF_1'(A_35))
      | v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ! [E_22,D_21] :
      ( v2_funct_1('#skF_5')
      | E_22 = D_21
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5',D_21)
      | ~ r2_hidden(E_22,'#skF_3')
      | ~ r2_hidden(D_21,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_81,plain,(
    ! [E_22,D_21] :
      ( E_22 = D_21
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5',D_21)
      | ~ r2_hidden(E_22,'#skF_3')
      | ~ r2_hidden(D_21,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_54])).

tff(c_93,plain,(
    ! [D_21] :
      ( D_21 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_21) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_21,'#skF_3')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_81])).

tff(c_102,plain,(
    ! [D_21] :
      ( D_21 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_21) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_21,'#skF_3')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34,c_93])).

tff(c_103,plain,(
    ! [D_21] :
      ( D_21 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_21) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_3')
      | ~ r2_hidden(D_21,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_102])).

tff(c_149,plain,(
    ! [D_21] :
      ( D_21 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_21) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(D_21,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_103])).

tff(c_152,plain,
    ( '#skF_2'('#skF_5') = '#skF_1'('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_149])).

tff(c_154,plain,(
    '#skF_2'('#skF_5') = '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_152])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_154])).

tff(c_158,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_157,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_163,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_157])).

tff(c_175,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_30])).

tff(c_176,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_180,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_175,c_176])).

tff(c_181,plain,(
    ! [A_51] :
      ( '#skF_2'(A_51) != '#skF_1'(A_51)
      | v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_184,plain,
    ( '#skF_2'('#skF_5') != '#skF_1'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_181,c_55])).

tff(c_187,plain,(
    '#skF_2'('#skF_5') != '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_34,c_184])).

tff(c_168,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_32])).

tff(c_197,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_201,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_175,c_197])).

tff(c_24,plain,(
    ! [B_15,C_16] :
      ( k1_relset_1(k1_xboole_0,B_15,C_16) = k1_xboole_0
      | ~ v1_funct_2(C_16,k1_xboole_0,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_246,plain,(
    ! [B_65,C_66] :
      ( k1_relset_1('#skF_4',B_65,C_66) = '#skF_4'
      | ~ v1_funct_2(C_66,'#skF_4',B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_65))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_158,c_158,c_158,c_24])).

tff(c_249,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_246])).

tff(c_252,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_201,c_249])).

tff(c_257,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_10])).

tff(c_264,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_34,c_257])).

tff(c_265,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_264])).

tff(c_260,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_8])).

tff(c_267,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_34,c_260])).

tff(c_268,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_267])).

tff(c_208,plain,(
    ! [A_60] :
      ( k1_funct_1(A_60,'#skF_2'(A_60)) = k1_funct_1(A_60,'#skF_1'(A_60))
      | v2_funct_1(A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_190,plain,(
    ! [E_22,D_21] :
      ( v2_funct_1('#skF_5')
      | E_22 = D_21
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5',D_21)
      | ~ r2_hidden(E_22,'#skF_4')
      | ~ r2_hidden(D_21,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_163,c_54])).

tff(c_191,plain,(
    ! [E_22,D_21] :
      ( E_22 = D_21
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5',D_21)
      | ~ r2_hidden(E_22,'#skF_4')
      | ~ r2_hidden(D_21,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_190])).

tff(c_217,plain,(
    ! [E_22] :
      ( E_22 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(E_22,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_191])).

tff(c_226,plain,(
    ! [E_22] :
      ( E_22 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(E_22,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_34,c_217])).

tff(c_227,plain,(
    ! [E_22] :
      ( E_22 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(E_22,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_226])).

tff(c_296,plain,(
    ! [E_22] :
      ( E_22 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',E_22) != k1_funct_1('#skF_5','#skF_1'('#skF_5'))
      | ~ r2_hidden(E_22,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_227])).

tff(c_299,plain,
    ( '#skF_2'('#skF_5') = '#skF_1'('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_296])).

tff(c_301,plain,(
    '#skF_2'('#skF_5') = '#skF_1'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_299])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_301])).

tff(c_304,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_305,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_310,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_42])).

tff(c_317,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_321,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_317])).

tff(c_306,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_327,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_331,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_327])).

tff(c_356,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_359,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_356])).

tff(c_362,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_331,c_359])).

tff(c_363,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_362])).

tff(c_40,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_308,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_40])).

tff(c_38,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_312,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_38])).

tff(c_389,plain,(
    ! [C_96,B_97,A_98] :
      ( C_96 = B_97
      | k1_funct_1(A_98,C_96) != k1_funct_1(A_98,B_97)
      | ~ r2_hidden(C_96,k1_relat_1(A_98))
      | ~ r2_hidden(B_97,k1_relat_1(A_98))
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_395,plain,(
    ! [B_97] :
      ( B_97 = '#skF_7'
      | k1_funct_1('#skF_5',B_97) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_97,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_389])).

tff(c_402,plain,(
    ! [B_99] :
      ( B_99 = '#skF_7'
      | k1_funct_1('#skF_5',B_99) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(B_99,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_34,c_305,c_363,c_308,c_363,c_395])).

tff(c_405,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_310,c_402])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_405])).

tff(c_414,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_413,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_421,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_413])).

tff(c_433,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_421,c_42])).

tff(c_434,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_30])).

tff(c_435,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_439,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_434,c_435])).

tff(c_427,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_32])).

tff(c_451,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_455,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_434,c_451])).

tff(c_479,plain,(
    ! [B_113,C_114] :
      ( k1_relset_1('#skF_4',B_113,C_114) = '#skF_4'
      | ~ v1_funct_2(C_114,'#skF_4',B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_113))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_414,c_414,c_414,c_24])).

tff(c_482,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_434,c_479])).

tff(c_485,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_455,c_482])).

tff(c_416,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_40])).

tff(c_426,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_416])).

tff(c_441,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_38])).

tff(c_540,plain,(
    ! [C_123,B_124,A_125] :
      ( C_123 = B_124
      | k1_funct_1(A_125,C_123) != k1_funct_1(A_125,B_124)
      | ~ r2_hidden(C_123,k1_relat_1(A_125))
      | ~ r2_hidden(B_124,k1_relat_1(A_125))
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_546,plain,(
    ! [B_124] :
      ( B_124 = '#skF_7'
      | k1_funct_1('#skF_5',B_124) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_124,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_540])).

tff(c_553,plain,(
    ! [B_126] :
      ( B_126 = '#skF_7'
      | k1_funct_1('#skF_5',B_126) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(B_126,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_34,c_305,c_485,c_426,c_485,c_546])).

tff(c_556,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_433,c_553])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.89  
% 3.24/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.89  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.24/1.89  
% 3.24/1.89  %Foreground sorts:
% 3.24/1.89  
% 3.24/1.89  
% 3.24/1.89  %Background operators:
% 3.24/1.89  
% 3.24/1.89  
% 3.24/1.89  %Foreground operators:
% 3.24/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.89  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.24/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.24/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.24/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.89  tff('#skF_7', type, '#skF_7': $i).
% 3.24/1.89  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.24/1.89  tff('#skF_6', type, '#skF_6': $i).
% 3.24/1.89  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.24/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.24/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.89  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.89  
% 3.62/1.92  tff(f_88, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (v2_funct_1(C) <=> (![D, E]: (((r2_hidden(D, A) & r2_hidden(E, A)) & (k1_funct_1(C, D) = k1_funct_1(C, E))) => (D = E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_funct_2)).
% 3.62/1.92  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.62/1.92  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 3.62/1.92  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.62/1.92  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.62/1.92  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_57, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.92  tff(c_61, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_57])).
% 3.62/1.92  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_62, plain, (![A_26]: ('#skF_2'(A_26)!='#skF_1'(A_26) | v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.92  tff(c_36, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_55, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_36])).
% 3.62/1.92  tff(c_65, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_55])).
% 3.62/1.92  tff(c_68, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_34, c_65])).
% 3.62/1.92  tff(c_28, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 3.62/1.92  tff(c_32, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_71, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.92  tff(c_75, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_71])).
% 3.62/1.92  tff(c_111, plain, (![B_42, A_43, C_44]: (k1_xboole_0=B_42 | k1_relset_1(A_43, B_42, C_44)=A_43 | ~v1_funct_2(C_44, A_43, B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.92  tff(c_114, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_111])).
% 3.62/1.92  tff(c_117, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75, c_114])).
% 3.62/1.92  tff(c_118, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_56, c_117])).
% 3.62/1.92  tff(c_10, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.92  tff(c_126, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_3') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_118, c_10])).
% 3.62/1.92  tff(c_133, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_3') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_34, c_126])).
% 3.62/1.92  tff(c_134, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_55, c_133])).
% 3.62/1.92  tff(c_8, plain, (![A_1]: (r2_hidden('#skF_2'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.92  tff(c_123, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_3') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_118, c_8])).
% 3.62/1.92  tff(c_130, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_3') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_34, c_123])).
% 3.62/1.92  tff(c_131, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_55, c_130])).
% 3.62/1.92  tff(c_87, plain, (![A_35]: (k1_funct_1(A_35, '#skF_2'(A_35))=k1_funct_1(A_35, '#skF_1'(A_35)) | v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.92  tff(c_54, plain, (![E_22, D_21]: (v2_funct_1('#skF_5') | E_22=D_21 | k1_funct_1('#skF_5', E_22)!=k1_funct_1('#skF_5', D_21) | ~r2_hidden(E_22, '#skF_3') | ~r2_hidden(D_21, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_81, plain, (![E_22, D_21]: (E_22=D_21 | k1_funct_1('#skF_5', E_22)!=k1_funct_1('#skF_5', D_21) | ~r2_hidden(E_22, '#skF_3') | ~r2_hidden(D_21, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_55, c_54])).
% 3.62/1.92  tff(c_93, plain, (![D_21]: (D_21='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_21)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_3') | ~r2_hidden(D_21, '#skF_3') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_81])).
% 3.62/1.92  tff(c_102, plain, (![D_21]: (D_21='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_21)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_3') | ~r2_hidden(D_21, '#skF_3') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_34, c_93])).
% 3.62/1.92  tff(c_103, plain, (![D_21]: (D_21='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_21)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_3') | ~r2_hidden(D_21, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_55, c_102])).
% 3.62/1.92  tff(c_149, plain, (![D_21]: (D_21='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_21)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden(D_21, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_103])).
% 3.62/1.92  tff(c_152, plain, ('#skF_2'('#skF_5')='#skF_1'('#skF_5') | ~r2_hidden('#skF_1'('#skF_5'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_149])).
% 3.62/1.92  tff(c_154, plain, ('#skF_2'('#skF_5')='#skF_1'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_152])).
% 3.62/1.92  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_154])).
% 3.62/1.92  tff(c_158, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 3.62/1.92  tff(c_157, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 3.62/1.92  tff(c_163, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_157])).
% 3.62/1.92  tff(c_175, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_30])).
% 3.62/1.92  tff(c_176, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.92  tff(c_180, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_175, c_176])).
% 3.62/1.92  tff(c_181, plain, (![A_51]: ('#skF_2'(A_51)!='#skF_1'(A_51) | v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.92  tff(c_184, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_181, c_55])).
% 3.62/1.92  tff(c_187, plain, ('#skF_2'('#skF_5')!='#skF_1'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_34, c_184])).
% 3.62/1.92  tff(c_168, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_32])).
% 3.62/1.92  tff(c_197, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.92  tff(c_201, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_175, c_197])).
% 3.62/1.92  tff(c_24, plain, (![B_15, C_16]: (k1_relset_1(k1_xboole_0, B_15, C_16)=k1_xboole_0 | ~v1_funct_2(C_16, k1_xboole_0, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.92  tff(c_246, plain, (![B_65, C_66]: (k1_relset_1('#skF_4', B_65, C_66)='#skF_4' | ~v1_funct_2(C_66, '#skF_4', B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_65))))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_158, c_158, c_158, c_24])).
% 3.62/1.92  tff(c_249, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_175, c_246])).
% 3.62/1.92  tff(c_252, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_201, c_249])).
% 3.62/1.92  tff(c_257, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_252, c_10])).
% 3.62/1.92  tff(c_264, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_34, c_257])).
% 3.62/1.92  tff(c_265, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_55, c_264])).
% 3.62/1.92  tff(c_260, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_252, c_8])).
% 3.62/1.92  tff(c_267, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_34, c_260])).
% 3.62/1.92  tff(c_268, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_55, c_267])).
% 3.62/1.92  tff(c_208, plain, (![A_60]: (k1_funct_1(A_60, '#skF_2'(A_60))=k1_funct_1(A_60, '#skF_1'(A_60)) | v2_funct_1(A_60) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.92  tff(c_190, plain, (![E_22, D_21]: (v2_funct_1('#skF_5') | E_22=D_21 | k1_funct_1('#skF_5', E_22)!=k1_funct_1('#skF_5', D_21) | ~r2_hidden(E_22, '#skF_4') | ~r2_hidden(D_21, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_163, c_54])).
% 3.62/1.92  tff(c_191, plain, (![E_22, D_21]: (E_22=D_21 | k1_funct_1('#skF_5', E_22)!=k1_funct_1('#skF_5', D_21) | ~r2_hidden(E_22, '#skF_4') | ~r2_hidden(D_21, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_55, c_190])).
% 3.62/1.92  tff(c_217, plain, (![E_22]: (E_22='#skF_2'('#skF_5') | k1_funct_1('#skF_5', E_22)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden(E_22, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_208, c_191])).
% 3.62/1.92  tff(c_226, plain, (![E_22]: (E_22='#skF_2'('#skF_5') | k1_funct_1('#skF_5', E_22)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden(E_22, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_34, c_217])).
% 3.62/1.92  tff(c_227, plain, (![E_22]: (E_22='#skF_2'('#skF_5') | k1_funct_1('#skF_5', E_22)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden(E_22, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_55, c_226])).
% 3.62/1.92  tff(c_296, plain, (![E_22]: (E_22='#skF_2'('#skF_5') | k1_funct_1('#skF_5', E_22)!=k1_funct_1('#skF_5', '#skF_1'('#skF_5')) | ~r2_hidden(E_22, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_227])).
% 3.62/1.92  tff(c_299, plain, ('#skF_2'('#skF_5')='#skF_1'('#skF_5') | ~r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_296])).
% 3.62/1.92  tff(c_301, plain, ('#skF_2'('#skF_5')='#skF_1'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_299])).
% 3.62/1.92  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_301])).
% 3.62/1.92  tff(c_304, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_36])).
% 3.62/1.92  tff(c_305, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 3.62/1.92  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_310, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_42])).
% 3.62/1.92  tff(c_317, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.92  tff(c_321, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_317])).
% 3.62/1.92  tff(c_306, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 3.62/1.92  tff(c_327, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.92  tff(c_331, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_327])).
% 3.62/1.92  tff(c_356, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.92  tff(c_359, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_356])).
% 3.62/1.92  tff(c_362, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_331, c_359])).
% 3.62/1.92  tff(c_363, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_306, c_362])).
% 3.62/1.92  tff(c_40, plain, (r2_hidden('#skF_7', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_308, plain, (r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_40])).
% 3.62/1.92  tff(c_38, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.92  tff(c_312, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_38])).
% 3.62/1.92  tff(c_389, plain, (![C_96, B_97, A_98]: (C_96=B_97 | k1_funct_1(A_98, C_96)!=k1_funct_1(A_98, B_97) | ~r2_hidden(C_96, k1_relat_1(A_98)) | ~r2_hidden(B_97, k1_relat_1(A_98)) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.92  tff(c_395, plain, (![B_97]: (B_97='#skF_7' | k1_funct_1('#skF_5', B_97)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~r2_hidden(B_97, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_312, c_389])).
% 3.62/1.92  tff(c_402, plain, (![B_99]: (B_99='#skF_7' | k1_funct_1('#skF_5', B_99)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden(B_99, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_34, c_305, c_363, c_308, c_363, c_395])).
% 3.62/1.92  tff(c_405, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_310, c_402])).
% 3.62/1.92  tff(c_412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_304, c_405])).
% 3.62/1.92  tff(c_414, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 3.62/1.92  tff(c_413, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 3.62/1.92  tff(c_421, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_414, c_413])).
% 3.62/1.92  tff(c_433, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_421, c_42])).
% 3.62/1.92  tff(c_434, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_30])).
% 3.62/1.92  tff(c_435, plain, (![C_100, A_101, B_102]: (v1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.92  tff(c_439, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_434, c_435])).
% 3.62/1.92  tff(c_427, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_421, c_32])).
% 3.62/1.92  tff(c_451, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.92  tff(c_455, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_434, c_451])).
% 3.62/1.92  tff(c_479, plain, (![B_113, C_114]: (k1_relset_1('#skF_4', B_113, C_114)='#skF_4' | ~v1_funct_2(C_114, '#skF_4', B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_113))))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_414, c_414, c_414, c_24])).
% 3.62/1.92  tff(c_482, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_434, c_479])).
% 3.62/1.92  tff(c_485, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_427, c_455, c_482])).
% 3.62/1.92  tff(c_416, plain, (r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_40])).
% 3.62/1.92  tff(c_426, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_421, c_416])).
% 3.62/1.92  tff(c_441, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_38])).
% 3.62/1.92  tff(c_540, plain, (![C_123, B_124, A_125]: (C_123=B_124 | k1_funct_1(A_125, C_123)!=k1_funct_1(A_125, B_124) | ~r2_hidden(C_123, k1_relat_1(A_125)) | ~r2_hidden(B_124, k1_relat_1(A_125)) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.92  tff(c_546, plain, (![B_124]: (B_124='#skF_7' | k1_funct_1('#skF_5', B_124)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~r2_hidden(B_124, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_441, c_540])).
% 3.62/1.92  tff(c_553, plain, (![B_126]: (B_126='#skF_7' | k1_funct_1('#skF_5', B_126)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden(B_126, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_34, c_305, c_485, c_426, c_485, c_546])).
% 3.62/1.92  tff(c_556, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_433, c_553])).
% 3.62/1.92  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_304, c_556])).
% 3.62/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.92  
% 3.62/1.92  Inference rules
% 3.62/1.92  ----------------------
% 3.62/1.92  #Ref     : 6
% 3.62/1.92  #Sup     : 96
% 3.62/1.92  #Fact    : 0
% 3.62/1.92  #Define  : 0
% 3.62/1.92  #Split   : 3
% 3.62/1.92  #Chain   : 0
% 3.62/1.92  #Close   : 0
% 3.62/1.92  
% 3.62/1.92  Ordering : KBO
% 3.62/1.92  
% 3.62/1.92  Simplification rules
% 3.62/1.92  ----------------------
% 3.62/1.92  #Subsume      : 15
% 3.62/1.93  #Demod        : 174
% 3.62/1.93  #Tautology    : 79
% 3.62/1.93  #SimpNegUnit  : 18
% 3.62/1.93  #BackRed      : 9
% 3.62/1.93  
% 3.62/1.93  #Partial instantiations: 0
% 3.62/1.93  #Strategies tried      : 1
% 3.62/1.93  
% 3.62/1.93  Timing (in seconds)
% 3.62/1.93  ----------------------
% 3.62/1.93  Preprocessing        : 0.52
% 3.62/1.93  Parsing              : 0.26
% 3.62/1.93  CNF conversion       : 0.04
% 3.62/1.93  Main loop            : 0.51
% 3.62/1.93  Inferencing          : 0.19
% 3.62/1.93  Reduction            : 0.15
% 3.62/1.93  Demodulation         : 0.11
% 3.62/1.93  BG Simplification    : 0.03
% 3.62/1.93  Subsumption          : 0.08
% 3.62/1.93  Abstraction          : 0.03
% 3.62/1.93  MUC search           : 0.00
% 3.62/1.93  Cooper               : 0.00
% 3.62/1.93  Total                : 1.12
% 3.62/1.93  Index Insertion      : 0.00
% 3.62/1.93  Index Deletion       : 0.00
% 3.62/1.93  Index Matching       : 0.00
% 3.62/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
