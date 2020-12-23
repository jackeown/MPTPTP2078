%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:29 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 201 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 503 expanded)
%              Number of equality atoms :   12 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_20,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_68,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_64])).

tff(c_170,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k7_relset_1(A_83,B_84,C_85,D_86) = k9_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_177,plain,(
    ! [D_86] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_86) = k9_relat_1('#skF_6',D_86) ),
    inference(resolution,[status(thm)],[c_42,c_170])).

tff(c_40,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_40])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_336,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden(k4_tarski('#skF_2'(A_113,B_114,C_115),A_113),C_115)
      | ~ r2_hidden(A_113,k9_relat_1(C_115,B_114))
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_456,plain,(
    ! [C_137,A_138,B_139] :
      ( k1_funct_1(C_137,'#skF_2'(A_138,B_139,C_137)) = A_138
      | ~ v1_funct_1(C_137)
      | ~ r2_hidden(A_138,k9_relat_1(C_137,B_139))
      | ~ v1_relat_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_336,c_32])).

tff(c_470,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_179,c_456])).

tff(c_486,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46,c_470])).

tff(c_78,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_48] : r1_tarski(A_48,A_48) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_49,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_57,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_64,B_65,B_66] :
      ( r2_hidden('#skF_1'(A_64,B_65),B_66)
      | ~ r1_tarski(A_64,B_66)
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_277,plain,(
    ! [A_101,B_102,B_103,B_104] :
      ( r2_hidden('#skF_1'(A_101,B_102),B_103)
      | ~ r1_tarski(B_104,B_103)
      | ~ r1_tarski(A_101,B_104)
      | r1_tarski(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_284,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_1'(A_105,B_106),k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_105,'#skF_6')
      | r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_57,c_277])).

tff(c_292,plain,(
    ! [A_105] :
      ( ~ r1_tarski(A_105,'#skF_6')
      | r1_tarski(A_105,k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_284,c_4])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_2'(A_17,B_18,C_19),k1_relat_1(C_19))
      | ~ r2_hidden(A_17,k9_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [A_23,C_25] :
      ( r2_hidden(k4_tarski(A_23,k1_funct_1(C_25,A_23)),C_25)
      | ~ r2_hidden(A_23,k1_relat_1(C_25))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_527,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_30])).

tff(c_531,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46,c_527])).

tff(c_533,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_539,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_533])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_179,c_539])).

tff(c_547,plain,(
    r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_619,plain,(
    ! [B_150] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),B_150)
      | ~ r1_tarski('#skF_6',B_150) ) ),
    inference(resolution,[status(thm)],[c_547,c_2])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_723,plain,(
    ! [C_163,D_164] :
      ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),C_163)
      | ~ r1_tarski('#skF_6',k2_zfmisc_1(C_163,D_164)) ) ),
    inference(resolution,[status(thm)],[c_619,c_12])).

tff(c_726,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_292,c_723])).

tff(c_731,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_726])).

tff(c_157,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_2'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden(A_77,k9_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [F_34] :
      ( k1_funct_1('#skF_6',F_34) != '#skF_7'
      | ~ r2_hidden(F_34,'#skF_5')
      | ~ r2_hidden(F_34,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_165,plain,(
    ! [A_77,C_79] :
      ( k1_funct_1('#skF_6','#skF_2'(A_77,'#skF_5',C_79)) != '#skF_7'
      | ~ r2_hidden('#skF_2'(A_77,'#skF_5',C_79),'#skF_3')
      | ~ r2_hidden(A_77,k9_relat_1(C_79,'#skF_5'))
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_157,c_38])).

tff(c_737,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_731,c_165])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_179,c_486,c_737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:42:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.44  
% 2.71/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.44  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.71/1.44  
% 2.71/1.44  %Foreground sorts:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Background operators:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Foreground operators:
% 2.71/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.71/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.71/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.71/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.44  
% 2.71/1.46  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.71/1.46  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.71/1.46  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.71/1.46  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.71/1.46  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.71/1.46  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.71/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.71/1.46  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.46  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.71/1.46  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.46  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.71/1.46  tff(c_58, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.71/1.46  tff(c_64, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.71/1.46  tff(c_68, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_64])).
% 2.71/1.46  tff(c_170, plain, (![A_83, B_84, C_85, D_86]: (k7_relset_1(A_83, B_84, C_85, D_86)=k9_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.71/1.46  tff(c_177, plain, (![D_86]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_86)=k9_relat_1('#skF_6', D_86))), inference(resolution, [status(thm)], [c_42, c_170])).
% 2.71/1.46  tff(c_40, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.71/1.46  tff(c_179, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_40])).
% 2.71/1.46  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.71/1.46  tff(c_336, plain, (![A_113, B_114, C_115]: (r2_hidden(k4_tarski('#skF_2'(A_113, B_114, C_115), A_113), C_115) | ~r2_hidden(A_113, k9_relat_1(C_115, B_114)) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.71/1.46  tff(c_32, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.71/1.46  tff(c_456, plain, (![C_137, A_138, B_139]: (k1_funct_1(C_137, '#skF_2'(A_138, B_139, C_137))=A_138 | ~v1_funct_1(C_137) | ~r2_hidden(A_138, k9_relat_1(C_137, B_139)) | ~v1_relat_1(C_137))), inference(resolution, [status(thm)], [c_336, c_32])).
% 2.71/1.46  tff(c_470, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_179, c_456])).
% 2.71/1.46  tff(c_486, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46, c_470])).
% 2.71/1.46  tff(c_78, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.46  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.46  tff(c_87, plain, (![A_48]: (r1_tarski(A_48, A_48))), inference(resolution, [status(thm)], [c_78, c_4])).
% 2.71/1.46  tff(c_49, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.46  tff(c_57, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_49])).
% 2.71/1.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.46  tff(c_94, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.46  tff(c_111, plain, (![A_64, B_65, B_66]: (r2_hidden('#skF_1'(A_64, B_65), B_66) | ~r1_tarski(A_64, B_66) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_6, c_94])).
% 2.71/1.46  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.46  tff(c_277, plain, (![A_101, B_102, B_103, B_104]: (r2_hidden('#skF_1'(A_101, B_102), B_103) | ~r1_tarski(B_104, B_103) | ~r1_tarski(A_101, B_104) | r1_tarski(A_101, B_102))), inference(resolution, [status(thm)], [c_111, c_2])).
% 2.71/1.46  tff(c_284, plain, (![A_105, B_106]: (r2_hidden('#skF_1'(A_105, B_106), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r1_tarski(A_105, '#skF_6') | r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_57, c_277])).
% 2.71/1.46  tff(c_292, plain, (![A_105]: (~r1_tarski(A_105, '#skF_6') | r1_tarski(A_105, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_284, c_4])).
% 2.71/1.46  tff(c_28, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_2'(A_17, B_18, C_19), k1_relat_1(C_19)) | ~r2_hidden(A_17, k9_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.71/1.46  tff(c_30, plain, (![A_23, C_25]: (r2_hidden(k4_tarski(A_23, k1_funct_1(C_25, A_23)), C_25) | ~r2_hidden(A_23, k1_relat_1(C_25)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.71/1.46  tff(c_527, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_486, c_30])).
% 2.71/1.46  tff(c_531, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46, c_527])).
% 2.71/1.46  tff(c_533, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_531])).
% 2.71/1.46  tff(c_539, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28, c_533])).
% 2.71/1.46  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_179, c_539])).
% 2.71/1.46  tff(c_547, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_531])).
% 2.71/1.46  tff(c_619, plain, (![B_150]: (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), B_150) | ~r1_tarski('#skF_6', B_150))), inference(resolution, [status(thm)], [c_547, c_2])).
% 2.71/1.46  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.71/1.46  tff(c_723, plain, (![C_163, D_164]: (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), C_163) | ~r1_tarski('#skF_6', k2_zfmisc_1(C_163, D_164)))), inference(resolution, [status(thm)], [c_619, c_12])).
% 2.71/1.46  tff(c_726, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3') | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_292, c_723])).
% 2.71/1.46  tff(c_731, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_726])).
% 2.71/1.46  tff(c_157, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_2'(A_77, B_78, C_79), B_78) | ~r2_hidden(A_77, k9_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.71/1.46  tff(c_38, plain, (![F_34]: (k1_funct_1('#skF_6', F_34)!='#skF_7' | ~r2_hidden(F_34, '#skF_5') | ~r2_hidden(F_34, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.71/1.46  tff(c_165, plain, (![A_77, C_79]: (k1_funct_1('#skF_6', '#skF_2'(A_77, '#skF_5', C_79))!='#skF_7' | ~r2_hidden('#skF_2'(A_77, '#skF_5', C_79), '#skF_3') | ~r2_hidden(A_77, k9_relat_1(C_79, '#skF_5')) | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_157, c_38])).
% 2.71/1.46  tff(c_737, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_731, c_165])).
% 2.71/1.46  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_179, c_486, c_737])).
% 2.71/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  Inference rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Ref     : 0
% 2.71/1.46  #Sup     : 146
% 2.71/1.46  #Fact    : 0
% 2.71/1.46  #Define  : 0
% 2.71/1.46  #Split   : 9
% 2.71/1.46  #Chain   : 0
% 2.71/1.46  #Close   : 0
% 2.71/1.46  
% 2.71/1.46  Ordering : KBO
% 2.71/1.46  
% 2.71/1.46  Simplification rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Subsume      : 6
% 2.71/1.46  #Demod        : 43
% 2.71/1.46  #Tautology    : 22
% 2.71/1.46  #SimpNegUnit  : 0
% 2.71/1.46  #BackRed      : 2
% 2.71/1.46  
% 2.71/1.46  #Partial instantiations: 0
% 2.71/1.46  #Strategies tried      : 1
% 2.71/1.46  
% 2.71/1.46  Timing (in seconds)
% 2.71/1.46  ----------------------
% 2.71/1.46  Preprocessing        : 0.31
% 2.71/1.46  Parsing              : 0.16
% 2.71/1.46  CNF conversion       : 0.02
% 2.71/1.46  Main loop            : 0.37
% 2.71/1.46  Inferencing          : 0.14
% 2.71/1.46  Reduction            : 0.10
% 2.71/1.46  Demodulation         : 0.07
% 2.71/1.46  BG Simplification    : 0.02
% 2.71/1.46  Subsumption          : 0.08
% 2.71/1.46  Abstraction          : 0.02
% 2.71/1.46  MUC search           : 0.00
% 2.71/1.46  Cooper               : 0.00
% 2.71/1.46  Total                : 0.71
% 2.71/1.46  Index Insertion      : 0.00
% 2.71/1.46  Index Deletion       : 0.00
% 2.71/1.46  Index Matching       : 0.00
% 3.07/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
