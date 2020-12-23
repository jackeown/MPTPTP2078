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
% DateTime   : Thu Dec  3 10:11:24 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 555 expanded)
%              Number of leaves         :   31 ( 207 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 (1794 expanded)
%              Number of equality atoms :   57 ( 798 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

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
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_28,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_70,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_36,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_75,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_36])).

tff(c_129,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden('#skF_1'(A_64,B_65,C_66),B_65)
      | k2_relset_1(A_64,B_65,C_66) = B_65
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_131,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_133,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_131])).

tff(c_134,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_133])).

tff(c_46,plain,(
    ! [D_32] :
      ( r2_hidden('#skF_6'(D_32),'#skF_3')
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_81,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_81])).

tff(c_135,plain,(
    ! [B_67,A_68,C_69] :
      ( k1_xboole_0 = B_67
      | k1_relset_1(A_68,B_67,C_69) = A_68
      | ~ v1_funct_2(C_69,A_68,B_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_138,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_135])).

tff(c_141,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_85,c_138])).

tff(c_142,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_56,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    ! [D_32] :
      ( k1_funct_1('#skF_5','#skF_6'(D_32)) = D_32
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_94,plain,(
    ! [A_56,C_57] :
      ( r2_hidden(k4_tarski(A_56,k1_funct_1(C_57,A_56)),C_57)
      | ~ r2_hidden(A_56,k1_relat_1(C_57))
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [D_32] :
      ( r2_hidden(k4_tarski('#skF_6'(D_32),D_32),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_32),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_94])).

tff(c_108,plain,(
    ! [D_32] :
      ( r2_hidden(k4_tarski('#skF_6'(D_32),D_32),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_32),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_42,c_103])).

tff(c_143,plain,(
    ! [D_32] :
      ( r2_hidden(k4_tarski('#skF_6'(D_32),D_32),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_32),'#skF_3')
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_108])).

tff(c_166,plain,(
    ! [E_71,A_72,B_73,C_74] :
      ( ~ r2_hidden(k4_tarski(E_71,'#skF_1'(A_72,B_73,C_74)),C_74)
      | k2_relset_1(A_72,B_73,C_74) = B_73
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_186,plain,(
    ! [A_79,B_80] :
      ( k2_relset_1(A_79,B_80,'#skF_5') = B_80
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_79,B_80,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_79,B_80,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_166])).

tff(c_191,plain,(
    ! [A_81,B_82] :
      ( k2_relset_1(A_81,B_82,'#skF_5') = B_82
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ r2_hidden('#skF_1'(A_81,B_82,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_186])).

tff(c_194,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_191])).

tff(c_197,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_194])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_197])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_2,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_214,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_2])).

tff(c_26,plain,(
    ! [C_28,A_26] :
      ( k1_xboole_0 = C_28
      | ~ v1_funct_2(C_28,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_229,plain,(
    ! [C_88,A_89] :
      ( C_88 = '#skF_4'
      | ~ v1_funct_2(C_88,A_89,'#skF_4')
      | A_89 = '#skF_4'
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_200,c_200,c_26])).

tff(c_232,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_235,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_232])).

tff(c_236,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_201,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_238,plain,(
    k1_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_201])).

tff(c_243,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_40])).

tff(c_239,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_85])).

tff(c_242,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_38])).

tff(c_32,plain,(
    ! [B_27,C_28] :
      ( k1_relset_1(k1_xboole_0,B_27,C_28) = k1_xboole_0
      | ~ v1_funct_2(C_28,k1_xboole_0,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_296,plain,(
    ! [B_95,C_96] :
      ( k1_relset_1('#skF_4',B_95,C_96) = '#skF_4'
      | ~ v1_funct_2(C_96,'#skF_4',B_95)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_95))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_200,c_200,c_32])).

tff(c_299,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_242,c_296])).

tff(c_302,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_239,c_299])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_302])).

tff(c_305,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_311,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_75])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:34:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 2.18/1.30  
% 2.18/1.30  %Foreground sorts:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Background operators:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Foreground operators:
% 2.18/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.18/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.18/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.30  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.18/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.30  
% 2.18/1.32  tff(f_99, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 2.18/1.32  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.18/1.32  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 2.18/1.32  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.18/1.32  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.18/1.32  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.18/1.32  tff(f_38, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.18/1.32  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.18/1.32  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.18/1.32  tff(c_70, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.32  tff(c_74, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_70])).
% 2.18/1.32  tff(c_36, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.18/1.32  tff(c_75, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_36])).
% 2.18/1.32  tff(c_129, plain, (![A_64, B_65, C_66]: (r2_hidden('#skF_1'(A_64, B_65, C_66), B_65) | k2_relset_1(A_64, B_65, C_66)=B_65 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.32  tff(c_131, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_129])).
% 2.18/1.32  tff(c_133, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_131])).
% 2.18/1.32  tff(c_134, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_75, c_133])).
% 2.18/1.32  tff(c_46, plain, (![D_32]: (r2_hidden('#skF_6'(D_32), '#skF_3') | ~r2_hidden(D_32, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.18/1.32  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.18/1.32  tff(c_81, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.32  tff(c_85, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_81])).
% 2.18/1.32  tff(c_135, plain, (![B_67, A_68, C_69]: (k1_xboole_0=B_67 | k1_relset_1(A_68, B_67, C_69)=A_68 | ~v1_funct_2(C_69, A_68, B_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.32  tff(c_138, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_135])).
% 2.18/1.32  tff(c_141, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_85, c_138])).
% 2.18/1.32  tff(c_142, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_141])).
% 2.18/1.32  tff(c_56, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.18/1.32  tff(c_60, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_56])).
% 2.18/1.32  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.18/1.32  tff(c_44, plain, (![D_32]: (k1_funct_1('#skF_5', '#skF_6'(D_32))=D_32 | ~r2_hidden(D_32, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.18/1.32  tff(c_94, plain, (![A_56, C_57]: (r2_hidden(k4_tarski(A_56, k1_funct_1(C_57, A_56)), C_57) | ~r2_hidden(A_56, k1_relat_1(C_57)) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.32  tff(c_103, plain, (![D_32]: (r2_hidden(k4_tarski('#skF_6'(D_32), D_32), '#skF_5') | ~r2_hidden('#skF_6'(D_32), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_32, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_94])).
% 2.18/1.32  tff(c_108, plain, (![D_32]: (r2_hidden(k4_tarski('#skF_6'(D_32), D_32), '#skF_5') | ~r2_hidden('#skF_6'(D_32), k1_relat_1('#skF_5')) | ~r2_hidden(D_32, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_42, c_103])).
% 2.18/1.32  tff(c_143, plain, (![D_32]: (r2_hidden(k4_tarski('#skF_6'(D_32), D_32), '#skF_5') | ~r2_hidden('#skF_6'(D_32), '#skF_3') | ~r2_hidden(D_32, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_108])).
% 2.18/1.32  tff(c_166, plain, (![E_71, A_72, B_73, C_74]: (~r2_hidden(k4_tarski(E_71, '#skF_1'(A_72, B_73, C_74)), C_74) | k2_relset_1(A_72, B_73, C_74)=B_73 | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.32  tff(c_186, plain, (![A_79, B_80]: (k2_relset_1(A_79, B_80, '#skF_5')=B_80 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~r2_hidden('#skF_6'('#skF_1'(A_79, B_80, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_79, B_80, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_143, c_166])).
% 2.18/1.32  tff(c_191, plain, (![A_81, B_82]: (k2_relset_1(A_81, B_82, '#skF_5')=B_82 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~r2_hidden('#skF_1'(A_81, B_82, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_186])).
% 2.18/1.32  tff(c_194, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_38, c_191])).
% 2.18/1.32  tff(c_197, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_194])).
% 2.18/1.32  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_197])).
% 2.18/1.32  tff(c_200, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_141])).
% 2.18/1.32  tff(c_2, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.18/1.32  tff(c_214, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_2])).
% 2.18/1.32  tff(c_26, plain, (![C_28, A_26]: (k1_xboole_0=C_28 | ~v1_funct_2(C_28, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.32  tff(c_229, plain, (![C_88, A_89]: (C_88='#skF_4' | ~v1_funct_2(C_88, A_89, '#skF_4') | A_89='#skF_4' | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_200, c_200, c_26])).
% 2.18/1.32  tff(c_232, plain, ('#skF_5'='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_229])).
% 2.18/1.32  tff(c_235, plain, ('#skF_5'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_232])).
% 2.18/1.32  tff(c_236, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_235])).
% 2.18/1.32  tff(c_201, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitRight, [status(thm)], [c_141])).
% 2.18/1.32  tff(c_238, plain, (k1_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_201])).
% 2.18/1.32  tff(c_243, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_40])).
% 2.18/1.32  tff(c_239, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_85])).
% 2.18/1.32  tff(c_242, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_38])).
% 2.18/1.32  tff(c_32, plain, (![B_27, C_28]: (k1_relset_1(k1_xboole_0, B_27, C_28)=k1_xboole_0 | ~v1_funct_2(C_28, k1_xboole_0, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.32  tff(c_296, plain, (![B_95, C_96]: (k1_relset_1('#skF_4', B_95, C_96)='#skF_4' | ~v1_funct_2(C_96, '#skF_4', B_95) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_95))))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_200, c_200, c_32])).
% 2.18/1.32  tff(c_299, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_242, c_296])).
% 2.18/1.32  tff(c_302, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_239, c_299])).
% 2.18/1.32  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_302])).
% 2.18/1.32  tff(c_305, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_235])).
% 2.18/1.32  tff(c_311, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_305, c_75])).
% 2.18/1.32  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_311])).
% 2.18/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  Inference rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Ref     : 0
% 2.18/1.32  #Sup     : 56
% 2.18/1.32  #Fact    : 0
% 2.18/1.32  #Define  : 0
% 2.18/1.32  #Split   : 2
% 2.18/1.32  #Chain   : 0
% 2.18/1.32  #Close   : 0
% 2.18/1.32  
% 2.18/1.32  Ordering : KBO
% 2.18/1.32  
% 2.18/1.32  Simplification rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Subsume      : 4
% 2.18/1.32  #Demod        : 76
% 2.18/1.32  #Tautology    : 34
% 2.18/1.32  #SimpNegUnit  : 3
% 2.18/1.32  #BackRed      : 29
% 2.18/1.32  
% 2.18/1.32  #Partial instantiations: 0
% 2.18/1.32  #Strategies tried      : 1
% 2.18/1.32  
% 2.18/1.32  Timing (in seconds)
% 2.18/1.32  ----------------------
% 2.18/1.32  Preprocessing        : 0.32
% 2.18/1.32  Parsing              : 0.17
% 2.18/1.32  CNF conversion       : 0.02
% 2.18/1.32  Main loop            : 0.23
% 2.18/1.32  Inferencing          : 0.08
% 2.18/1.32  Reduction            : 0.07
% 2.18/1.32  Demodulation         : 0.05
% 2.18/1.32  BG Simplification    : 0.02
% 2.18/1.32  Subsumption          : 0.04
% 2.18/1.32  Abstraction          : 0.01
% 2.18/1.32  MUC search           : 0.00
% 2.18/1.32  Cooper               : 0.00
% 2.18/1.32  Total                : 0.59
% 2.18/1.32  Index Insertion      : 0.00
% 2.18/1.32  Index Deletion       : 0.00
% 2.18/1.32  Index Matching       : 0.00
% 2.18/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
