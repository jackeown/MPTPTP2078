%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:12 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 144 expanded)
%              Number of leaves         :   34 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 263 expanded)
%              Number of equality atoms :   31 (  87 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_38,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_55,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_61,plain,(
    ! [A_58] :
      ( k2_relat_1(A_58) = k1_xboole_0
      | k1_relat_1(A_58) != k1_xboole_0
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_61])).

tff(c_66,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_67,plain,(
    ! [A_59] :
      ( k1_relat_1(A_59) = k1_xboole_0
      | k2_relat_1(A_59) != k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_67])).

tff(c_73,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_70])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_207,plain,(
    ! [A_92,B_93] :
      ( r2_hidden(k4_tarski('#skF_1'(A_92,B_93),'#skF_2'(A_92,B_93)),A_92)
      | r2_hidden('#skF_3'(A_92,B_93),B_93)
      | k1_relat_1(A_92) = B_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [C_80,A_81] :
      ( r2_hidden(k4_tarski(C_80,'#skF_4'(A_81,k1_relat_1(A_81),C_80)),A_81)
      | ~ r2_hidden(C_80,k1_relat_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [C_80] :
      ( r2_hidden(k4_tarski(C_80,'#skF_4'(k1_xboole_0,k1_xboole_0,C_80)),k1_xboole_0)
      | ~ r2_hidden(C_80,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_144])).

tff(c_168,plain,(
    ! [C_83] :
      ( r2_hidden(k4_tarski(C_83,'#skF_4'(k1_xboole_0,k1_xboole_0,C_83)),k1_xboole_0)
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_161])).

tff(c_26,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_174,plain,(
    ! [C_83] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_83,'#skF_4'(k1_xboole_0,k1_xboole_0,C_83)))
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_168,c_26])).

tff(c_179,plain,(
    ! [C_83] : ~ r2_hidden(C_83,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_174])).

tff(c_211,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_93),B_93)
      | k1_relat_1(k1_xboole_0) = B_93 ) ),
    inference(resolution,[status(thm)],[c_207,c_179])).

tff(c_232,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_94),B_94)
      | k1_xboole_0 = B_94 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_211])).

tff(c_80,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_111,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k2_relset_1(A_76,B_77,C_78),k1_zfmisc_1(B_77))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_111])).

tff(c_134,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_128])).

tff(c_4,plain,(
    ! [A_2,C_4,B_3] :
      ( m1_subset_1(A_2,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_137,plain,(
    ! [A_2] :
      ( m1_subset_1(A_2,'#skF_6')
      | ~ r2_hidden(A_2,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_240,plain,
    ( m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_232,c_137])).

tff(c_252,plain,(
    m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_240])).

tff(c_36,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_relset_1('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(D_50,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_85,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_relat_1('#skF_7'))
      | ~ m1_subset_1(D_50,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_36])).

tff(c_244,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_232,c_85])).

tff(c_255,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_244])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_255])).

tff(c_260,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_294,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_297,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_294])).

tff(c_299,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_297])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.44  
% 2.54/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.54/1.44  
% 2.54/1.44  %Foreground sorts:
% 2.54/1.44  
% 2.54/1.44  
% 2.54/1.44  %Background operators:
% 2.54/1.44  
% 2.54/1.44  
% 2.54/1.44  %Foreground operators:
% 2.54/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.54/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.54/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.54/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.54/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.44  
% 2.54/1.45  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.54/1.45  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.54/1.45  tff(f_50, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.54/1.45  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.54/1.45  tff(f_41, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.54/1.45  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.54/1.45  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.54/1.45  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.54/1.45  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.54/1.45  tff(f_33, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.54/1.45  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.54/1.45  tff(c_38, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.45  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.45  tff(c_55, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.54/1.45  tff(c_59, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_55])).
% 2.54/1.45  tff(c_61, plain, (![A_58]: (k2_relat_1(A_58)=k1_xboole_0 | k1_relat_1(A_58)!=k1_xboole_0 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.45  tff(c_65, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_61])).
% 2.54/1.45  tff(c_66, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_65])).
% 2.54/1.45  tff(c_67, plain, (![A_59]: (k1_relat_1(A_59)=k1_xboole_0 | k2_relat_1(A_59)!=k1_xboole_0 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.45  tff(c_70, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_67])).
% 2.54/1.45  tff(c_73, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_70])).
% 2.54/1.45  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.54/1.45  tff(c_207, plain, (![A_92, B_93]: (r2_hidden(k4_tarski('#skF_1'(A_92, B_93), '#skF_2'(A_92, B_93)), A_92) | r2_hidden('#skF_3'(A_92, B_93), B_93) | k1_relat_1(A_92)=B_93)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.45  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.54/1.45  tff(c_144, plain, (![C_80, A_81]: (r2_hidden(k4_tarski(C_80, '#skF_4'(A_81, k1_relat_1(A_81), C_80)), A_81) | ~r2_hidden(C_80, k1_relat_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.45  tff(c_161, plain, (![C_80]: (r2_hidden(k4_tarski(C_80, '#skF_4'(k1_xboole_0, k1_xboole_0, C_80)), k1_xboole_0) | ~r2_hidden(C_80, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_144])).
% 2.54/1.45  tff(c_168, plain, (![C_83]: (r2_hidden(k4_tarski(C_83, '#skF_4'(k1_xboole_0, k1_xboole_0, C_83)), k1_xboole_0) | ~r2_hidden(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_161])).
% 2.54/1.45  tff(c_26, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.45  tff(c_174, plain, (![C_83]: (~r1_tarski(k1_xboole_0, k4_tarski(C_83, '#skF_4'(k1_xboole_0, k1_xboole_0, C_83))) | ~r2_hidden(C_83, k1_xboole_0))), inference(resolution, [status(thm)], [c_168, c_26])).
% 2.54/1.45  tff(c_179, plain, (![C_83]: (~r2_hidden(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_174])).
% 2.54/1.45  tff(c_211, plain, (![B_93]: (r2_hidden('#skF_3'(k1_xboole_0, B_93), B_93) | k1_relat_1(k1_xboole_0)=B_93)), inference(resolution, [status(thm)], [c_207, c_179])).
% 2.54/1.45  tff(c_232, plain, (![B_94]: (r2_hidden('#skF_3'(k1_xboole_0, B_94), B_94) | k1_xboole_0=B_94)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_211])).
% 2.54/1.45  tff(c_80, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.54/1.45  tff(c_84, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_80])).
% 2.54/1.45  tff(c_111, plain, (![A_76, B_77, C_78]: (m1_subset_1(k2_relset_1(A_76, B_77, C_78), k1_zfmisc_1(B_77)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.54/1.45  tff(c_128, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_111])).
% 2.54/1.45  tff(c_134, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_128])).
% 2.54/1.45  tff(c_4, plain, (![A_2, C_4, B_3]: (m1_subset_1(A_2, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.45  tff(c_137, plain, (![A_2]: (m1_subset_1(A_2, '#skF_6') | ~r2_hidden(A_2, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_134, c_4])).
% 2.54/1.45  tff(c_240, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_232, c_137])).
% 2.54/1.45  tff(c_252, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_73, c_240])).
% 2.54/1.45  tff(c_36, plain, (![D_50]: (~r2_hidden(D_50, k2_relset_1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1(D_50, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.45  tff(c_85, plain, (![D_50]: (~r2_hidden(D_50, k2_relat_1('#skF_7')) | ~m1_subset_1(D_50, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_36])).
% 2.54/1.45  tff(c_244, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_232, c_85])).
% 2.54/1.45  tff(c_255, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_73, c_244])).
% 2.54/1.45  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_255])).
% 2.54/1.45  tff(c_260, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_65])).
% 2.54/1.45  tff(c_294, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.54/1.45  tff(c_297, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_294])).
% 2.54/1.45  tff(c_299, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_260, c_297])).
% 2.54/1.45  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_299])).
% 2.54/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.45  
% 2.54/1.45  Inference rules
% 2.54/1.45  ----------------------
% 2.54/1.45  #Ref     : 0
% 2.54/1.45  #Sup     : 53
% 2.54/1.45  #Fact    : 0
% 2.54/1.45  #Define  : 0
% 2.54/1.45  #Split   : 1
% 2.54/1.45  #Chain   : 0
% 2.54/1.45  #Close   : 0
% 2.54/1.45  
% 2.54/1.45  Ordering : KBO
% 2.54/1.45  
% 2.54/1.45  Simplification rules
% 2.54/1.45  ----------------------
% 2.54/1.45  #Subsume      : 6
% 2.54/1.45  #Demod        : 17
% 2.54/1.45  #Tautology    : 18
% 2.54/1.45  #SimpNegUnit  : 5
% 2.54/1.45  #BackRed      : 3
% 2.54/1.45  
% 2.54/1.45  #Partial instantiations: 0
% 2.54/1.45  #Strategies tried      : 1
% 2.54/1.45  
% 2.54/1.45  Timing (in seconds)
% 2.54/1.45  ----------------------
% 2.54/1.46  Preprocessing        : 0.38
% 2.54/1.46  Parsing              : 0.20
% 2.54/1.46  CNF conversion       : 0.03
% 2.54/1.46  Main loop            : 0.23
% 2.54/1.46  Inferencing          : 0.09
% 2.54/1.46  Reduction            : 0.07
% 2.54/1.46  Demodulation         : 0.04
% 2.54/1.46  BG Simplification    : 0.02
% 2.54/1.46  Subsumption          : 0.04
% 2.54/1.46  Abstraction          : 0.02
% 2.54/1.46  MUC search           : 0.00
% 2.54/1.46  Cooper               : 0.00
% 2.54/1.46  Total                : 0.64
% 2.54/1.46  Index Insertion      : 0.00
% 2.54/1.46  Index Deletion       : 0.00
% 2.54/1.46  Index Matching       : 0.00
% 2.54/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
