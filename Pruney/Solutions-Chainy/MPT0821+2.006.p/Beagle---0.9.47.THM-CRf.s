%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:09 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 157 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 288 expanded)
%              Number of equality atoms :   22 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_30,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_88,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_92,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_231,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_235,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_231])).

tff(c_44,plain,
    ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_73,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_236,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_73])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_103,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_99])).

tff(c_104,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_73])).

tff(c_46,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski(D_44,'#skF_9'(D_44)),'#skF_8')
      | ~ r2_hidden(D_44,'#skF_7')
      | r2_hidden('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_93,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_50,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski(D_44,'#skF_9'(D_44)),'#skF_8')
      | ~ r2_hidden(D_44,'#skF_7')
      | k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_122,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski(D_44,'#skF_9'(D_44)),'#skF_8')
      | ~ r2_hidden(D_44,'#skF_7')
      | k1_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_50])).

tff(c_124,plain,(
    ! [D_82] :
      ( r2_hidden(k4_tarski(D_82,'#skF_9'(D_82)),'#skF_8')
      | ~ r2_hidden(D_82,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_122])).

tff(c_42,plain,(
    ! [D_44,E_47] :
      ( r2_hidden(k4_tarski(D_44,'#skF_9'(D_44)),'#skF_8')
      | ~ r2_hidden(D_44,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',E_47),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,(
    ! [E_47] : ~ r2_hidden(k4_tarski('#skF_10',E_47),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_128,plain,(
    ~ r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_124,c_115])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_128])).

tff(c_137,plain,(
    ! [D_83] :
      ( r2_hidden(k4_tarski(D_83,'#skF_9'(D_83)),'#skF_8')
      | ~ r2_hidden(D_83,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_20,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k1_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(C_26,D_29),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_142,plain,(
    ! [D_84] :
      ( r2_hidden(D_84,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_84,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_137,c_20])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),A_3)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_179,plain,(
    ! [B_88] :
      ( ~ r2_xboole_0(k1_relat_1('#skF_8'),B_88)
      | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_8'),B_88),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_142,c_8])).

tff(c_184,plain,(
    ~ r2_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_179])).

tff(c_189,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_184])).

tff(c_192,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_189])).

tff(c_195,plain,
    ( ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_92,c_195])).

tff(c_209,plain,(
    ! [D_92] :
      ( r2_hidden(k4_tarski(D_92,'#skF_9'(D_92)),'#skF_8')
      | ~ r2_hidden(D_92,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_219,plain,(
    ! [D_93] :
      ( r2_hidden(D_93,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_93,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_209,c_20])).

tff(c_241,plain,(
    ! [B_99] :
      ( ~ r2_xboole_0(k1_relat_1('#skF_8'),B_99)
      | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_8'),B_99),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_219,c_8])).

tff(c_246,plain,(
    ~ r2_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_241])).

tff(c_251,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_246])).

tff(c_254,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_251])).

tff(c_257,plain,
    ( ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_254])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_92,c_257])).

tff(c_262,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_263,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_294,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_297,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_294])).

tff(c_299,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_297])).

tff(c_325,plain,(
    ! [C_121,A_122] :
      ( r2_hidden(k4_tarski(C_121,'#skF_5'(A_122,k1_relat_1(A_122),C_121)),A_122)
      | ~ r2_hidden(C_121,k1_relat_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [E_47] :
      ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski('#skF_10',E_47),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_282,plain,(
    ! [E_47] : ~ r2_hidden(k4_tarski('#skF_10',E_47),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_40])).

tff(c_329,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_325,c_282])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_299,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:35:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.33  
% 2.27/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.33  %$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.27/1.33  
% 2.27/1.33  %Foreground sorts:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Background operators:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Foreground operators:
% 2.27/1.33  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.27/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.27/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.27/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.33  tff('#skF_10', type, '#skF_10': $i).
% 2.27/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.27/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.33  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.27/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.27/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.33  
% 2.27/1.35  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.27/1.35  tff(f_88, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.27/1.35  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.27/1.35  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.35  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.27/1.35  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.27/1.35  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.27/1.35  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.27/1.35  tff(f_63, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.27/1.35  tff(c_30, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.27/1.35  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.35  tff(c_54, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.35  tff(c_57, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_54])).
% 2.27/1.35  tff(c_60, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_57])).
% 2.27/1.35  tff(c_88, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.27/1.35  tff(c_92, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_88])).
% 2.27/1.35  tff(c_16, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.35  tff(c_231, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.27/1.35  tff(c_235, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_231])).
% 2.27/1.35  tff(c_44, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.35  tff(c_73, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_44])).
% 2.27/1.35  tff(c_236, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_235, c_73])).
% 2.27/1.35  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.35  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.35  tff(c_99, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.27/1.35  tff(c_103, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_99])).
% 2.27/1.35  tff(c_104, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_73])).
% 2.27/1.35  tff(c_46, plain, (![D_44]: (r2_hidden(k4_tarski(D_44, '#skF_9'(D_44)), '#skF_8') | ~r2_hidden(D_44, '#skF_7') | r2_hidden('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.35  tff(c_93, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_46])).
% 2.27/1.35  tff(c_50, plain, (![D_44]: (r2_hidden(k4_tarski(D_44, '#skF_9'(D_44)), '#skF_8') | ~r2_hidden(D_44, '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.35  tff(c_122, plain, (![D_44]: (r2_hidden(k4_tarski(D_44, '#skF_9'(D_44)), '#skF_8') | ~r2_hidden(D_44, '#skF_7') | k1_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_50])).
% 2.27/1.35  tff(c_124, plain, (![D_82]: (r2_hidden(k4_tarski(D_82, '#skF_9'(D_82)), '#skF_8') | ~r2_hidden(D_82, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_104, c_122])).
% 2.27/1.35  tff(c_42, plain, (![D_44, E_47]: (r2_hidden(k4_tarski(D_44, '#skF_9'(D_44)), '#skF_8') | ~r2_hidden(D_44, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', E_47), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.35  tff(c_115, plain, (![E_47]: (~r2_hidden(k4_tarski('#skF_10', E_47), '#skF_8'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.27/1.35  tff(c_128, plain, (~r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_124, c_115])).
% 2.27/1.35  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_128])).
% 2.27/1.35  tff(c_137, plain, (![D_83]: (r2_hidden(k4_tarski(D_83, '#skF_9'(D_83)), '#skF_8') | ~r2_hidden(D_83, '#skF_7'))), inference(splitRight, [status(thm)], [c_42])).
% 2.27/1.35  tff(c_20, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k1_relat_1(A_11)) | ~r2_hidden(k4_tarski(C_26, D_29), A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.27/1.35  tff(c_142, plain, (![D_84]: (r2_hidden(D_84, k1_relat_1('#skF_8')) | ~r2_hidden(D_84, '#skF_7'))), inference(resolution, [status(thm)], [c_137, c_20])).
% 2.27/1.35  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), A_3) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.35  tff(c_179, plain, (![B_88]: (~r2_xboole_0(k1_relat_1('#skF_8'), B_88) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_8'), B_88), '#skF_7'))), inference(resolution, [status(thm)], [c_142, c_8])).
% 2.27/1.35  tff(c_184, plain, (~r2_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_10, c_179])).
% 2.27/1.35  tff(c_189, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_2, c_184])).
% 2.27/1.35  tff(c_192, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_104, c_189])).
% 2.27/1.35  tff(c_195, plain, (~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_16, c_192])).
% 2.27/1.35  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_92, c_195])).
% 2.27/1.35  tff(c_209, plain, (![D_92]: (r2_hidden(k4_tarski(D_92, '#skF_9'(D_92)), '#skF_8') | ~r2_hidden(D_92, '#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 2.27/1.35  tff(c_219, plain, (![D_93]: (r2_hidden(D_93, k1_relat_1('#skF_8')) | ~r2_hidden(D_93, '#skF_7'))), inference(resolution, [status(thm)], [c_209, c_20])).
% 2.27/1.35  tff(c_241, plain, (![B_99]: (~r2_xboole_0(k1_relat_1('#skF_8'), B_99) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_8'), B_99), '#skF_7'))), inference(resolution, [status(thm)], [c_219, c_8])).
% 2.27/1.35  tff(c_246, plain, (~r2_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_10, c_241])).
% 2.27/1.35  tff(c_251, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_2, c_246])).
% 2.27/1.35  tff(c_254, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_236, c_251])).
% 2.27/1.35  tff(c_257, plain, (~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_16, c_254])).
% 2.27/1.35  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_92, c_257])).
% 2.27/1.35  tff(c_262, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 2.27/1.35  tff(c_263, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 2.27/1.35  tff(c_294, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.27/1.35  tff(c_297, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_294])).
% 2.27/1.35  tff(c_299, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_297])).
% 2.27/1.35  tff(c_325, plain, (![C_121, A_122]: (r2_hidden(k4_tarski(C_121, '#skF_5'(A_122, k1_relat_1(A_122), C_121)), A_122) | ~r2_hidden(C_121, k1_relat_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.27/1.35  tff(c_40, plain, (![E_47]: (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski('#skF_10', E_47), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.35  tff(c_282, plain, (![E_47]: (~r2_hidden(k4_tarski('#skF_10', E_47), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_40])).
% 2.27/1.35  tff(c_329, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_325, c_282])).
% 2.27/1.35  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_299, c_329])).
% 2.27/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  Inference rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Ref     : 0
% 2.27/1.35  #Sup     : 52
% 2.27/1.35  #Fact    : 0
% 2.27/1.35  #Define  : 0
% 2.27/1.35  #Split   : 5
% 2.27/1.35  #Chain   : 0
% 2.27/1.35  #Close   : 0
% 2.27/1.35  
% 2.27/1.35  Ordering : KBO
% 2.27/1.35  
% 2.27/1.35  Simplification rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Subsume      : 7
% 2.27/1.35  #Demod        : 18
% 2.27/1.35  #Tautology    : 17
% 2.27/1.35  #SimpNegUnit  : 5
% 2.27/1.35  #BackRed      : 2
% 2.27/1.35  
% 2.27/1.35  #Partial instantiations: 0
% 2.27/1.35  #Strategies tried      : 1
% 2.27/1.35  
% 2.27/1.35  Timing (in seconds)
% 2.27/1.35  ----------------------
% 2.27/1.35  Preprocessing        : 0.32
% 2.27/1.35  Parsing              : 0.17
% 2.27/1.35  CNF conversion       : 0.02
% 2.27/1.35  Main loop            : 0.21
% 2.27/1.35  Inferencing          : 0.08
% 2.27/1.35  Reduction            : 0.06
% 2.27/1.35  Demodulation         : 0.04
% 2.27/1.35  BG Simplification    : 0.01
% 2.27/1.35  Subsumption          : 0.04
% 2.27/1.35  Abstraction          : 0.01
% 2.27/1.36  MUC search           : 0.00
% 2.27/1.36  Cooper               : 0.00
% 2.27/1.36  Total                : 0.57
% 2.27/1.36  Index Insertion      : 0.00
% 2.27/1.36  Index Deletion       : 0.00
% 2.27/1.36  Index Matching       : 0.00
% 2.27/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
