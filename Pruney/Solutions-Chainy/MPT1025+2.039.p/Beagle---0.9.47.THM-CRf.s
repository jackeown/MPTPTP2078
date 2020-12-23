%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:35 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 230 expanded)
%              Number of leaves         :   35 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  133 ( 575 expanded)
%              Number of equality atoms :   17 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_82,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_98,plain,(
    ! [C_56,A_57,B_58] :
      ( v4_relat_1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_98])).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_77,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_74])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_209,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_relset_1(A_89,B_90,C_91,D_92) = k9_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_220,plain,(
    ! [D_92] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_92) = k9_relat_1('#skF_6',D_92) ),
    inference(resolution,[status(thm)],[c_42,c_209])).

tff(c_40,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_231,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_40])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden('#skF_2'(A_15,B_16,C_17),k1_relat_1(C_17))
      | ~ r2_hidden(A_15,k9_relat_1(C_17,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_273,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(k4_tarski('#skF_2'(A_100,B_101,C_102),A_100),C_102)
      | ~ r2_hidden(A_100,k9_relat_1(C_102,B_101))
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_funct_1(C_23,A_21) = B_22
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_449,plain,(
    ! [C_139,A_140,B_141] :
      ( k1_funct_1(C_139,'#skF_2'(A_140,B_141,C_139)) = A_140
      | ~ v1_funct_1(C_139)
      | ~ r2_hidden(A_140,k9_relat_1(C_139,B_141))
      | ~ v1_relat_1(C_139) ) ),
    inference(resolution,[status(thm)],[c_273,c_28])).

tff(c_460,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_231,c_449])).

tff(c_475,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_46,c_460])).

tff(c_354,plain,(
    ! [A_126,C_127] :
      ( r2_hidden(k4_tarski(A_126,k1_funct_1(C_127,A_126)),C_127)
      | ~ r2_hidden(A_126,k1_relat_1(C_127))
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_384,plain,(
    ! [A_126,C_127] :
      ( m1_subset_1(k4_tarski(A_126,k1_funct_1(C_127,A_126)),C_127)
      | ~ r2_hidden(A_126,k1_relat_1(C_127))
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_354,c_8])).

tff(c_482,plain,
    ( m1_subset_1(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_384])).

tff(c_489,plain,
    ( m1_subset_1(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_46,c_482])).

tff(c_493,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_489])).

tff(c_524,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_493])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_231,c_524])).

tff(c_533,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_489])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_578,plain,(
    ! [B_149] :
      ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),B_149)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_149) ) ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_611,plain,(
    ! [B_150] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),B_150)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_150) ) ),
    inference(resolution,[status(thm)],[c_578,c_8])).

tff(c_615,plain,(
    ! [A_11] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),A_11)
      | ~ v4_relat_1('#skF_6',A_11)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_14,c_611])).

tff(c_625,plain,(
    ! [A_151] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),A_151)
      | ~ v4_relat_1('#skF_6',A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_615])).

tff(c_167,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden('#skF_2'(A_79,B_80,C_81),B_80)
      | ~ r2_hidden(A_79,k9_relat_1(C_81,B_80))
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [F_35] :
      ( k1_funct_1('#skF_6',F_35) != '#skF_7'
      | ~ r2_hidden(F_35,'#skF_5')
      | ~ m1_subset_1(F_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_307,plain,(
    ! [A_113,C_114] :
      ( k1_funct_1('#skF_6','#skF_2'(A_113,'#skF_5',C_114)) != '#skF_7'
      | ~ m1_subset_1('#skF_2'(A_113,'#skF_5',C_114),'#skF_3')
      | ~ r2_hidden(A_113,k9_relat_1(C_114,'#skF_5'))
      | ~ v1_relat_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_167,c_38])).

tff(c_314,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_231,c_307])).

tff(c_330,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_314])).

tff(c_334,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_628,plain,(
    ~ v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_625,c_334])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_628])).

tff(c_648,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_789,plain,(
    ! [C_180,A_181,B_182] :
      ( k1_funct_1(C_180,'#skF_2'(A_181,B_182,C_180)) = A_181
      | ~ v1_funct_1(C_180)
      | ~ r2_hidden(A_181,k9_relat_1(C_180,B_182))
      | ~ v1_relat_1(C_180) ) ),
    inference(resolution,[status(thm)],[c_273,c_28])).

tff(c_800,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_231,c_789])).

tff(c_815,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_46,c_800])).

tff(c_817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n019.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 13:14:07 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.36  
% 2.91/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.91/1.37  
% 2.91/1.37  %Foreground sorts:
% 2.91/1.37  
% 2.91/1.37  
% 2.91/1.37  %Background operators:
% 2.91/1.37  
% 2.91/1.37  
% 2.91/1.37  %Foreground operators:
% 2.91/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.91/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.37  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.91/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.91/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.91/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.91/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.91/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.91/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.91/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.37  
% 3.17/1.40  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 3.17/1.40  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.17/1.40  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.17/1.40  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.17/1.40  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.17/1.40  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.17/1.40  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.17/1.40  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.17/1.40  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.17/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.17/1.40  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.17/1.40  tff(c_98, plain, (![C_56, A_57, B_58]: (v4_relat_1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.17/1.40  tff(c_107, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_98])).
% 3.17/1.40  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.17/1.40  tff(c_71, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.40  tff(c_74, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_71])).
% 3.17/1.40  tff(c_77, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_74])).
% 3.17/1.40  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.17/1.40  tff(c_209, plain, (![A_89, B_90, C_91, D_92]: (k7_relset_1(A_89, B_90, C_91, D_92)=k9_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.17/1.40  tff(c_220, plain, (![D_92]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_92)=k9_relat_1('#skF_6', D_92))), inference(resolution, [status(thm)], [c_42, c_209])).
% 3.17/1.40  tff(c_40, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.17/1.40  tff(c_231, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_40])).
% 3.17/1.40  tff(c_24, plain, (![A_15, B_16, C_17]: (r2_hidden('#skF_2'(A_15, B_16, C_17), k1_relat_1(C_17)) | ~r2_hidden(A_15, k9_relat_1(C_17, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.40  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.17/1.40  tff(c_273, plain, (![A_100, B_101, C_102]: (r2_hidden(k4_tarski('#skF_2'(A_100, B_101, C_102), A_100), C_102) | ~r2_hidden(A_100, k9_relat_1(C_102, B_101)) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.40  tff(c_28, plain, (![C_23, A_21, B_22]: (k1_funct_1(C_23, A_21)=B_22 | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.17/1.40  tff(c_449, plain, (![C_139, A_140, B_141]: (k1_funct_1(C_139, '#skF_2'(A_140, B_141, C_139))=A_140 | ~v1_funct_1(C_139) | ~r2_hidden(A_140, k9_relat_1(C_139, B_141)) | ~v1_relat_1(C_139))), inference(resolution, [status(thm)], [c_273, c_28])).
% 3.17/1.40  tff(c_460, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_231, c_449])).
% 3.17/1.40  tff(c_475, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_46, c_460])).
% 3.17/1.40  tff(c_354, plain, (![A_126, C_127]: (r2_hidden(k4_tarski(A_126, k1_funct_1(C_127, A_126)), C_127) | ~r2_hidden(A_126, k1_relat_1(C_127)) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.17/1.40  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.40  tff(c_384, plain, (![A_126, C_127]: (m1_subset_1(k4_tarski(A_126, k1_funct_1(C_127, A_126)), C_127) | ~r2_hidden(A_126, k1_relat_1(C_127)) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_354, c_8])).
% 3.17/1.40  tff(c_482, plain, (m1_subset_1(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_475, c_384])).
% 3.17/1.40  tff(c_489, plain, (m1_subset_1(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_46, c_482])).
% 3.17/1.40  tff(c_493, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_489])).
% 3.17/1.40  tff(c_524, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_493])).
% 3.17/1.40  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_231, c_524])).
% 3.17/1.40  tff(c_533, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_489])).
% 3.17/1.40  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.40  tff(c_578, plain, (![B_149]: (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), B_149) | ~r1_tarski(k1_relat_1('#skF_6'), B_149))), inference(resolution, [status(thm)], [c_533, c_2])).
% 3.17/1.40  tff(c_611, plain, (![B_150]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), B_150) | ~r1_tarski(k1_relat_1('#skF_6'), B_150))), inference(resolution, [status(thm)], [c_578, c_8])).
% 3.17/1.40  tff(c_615, plain, (![A_11]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), A_11) | ~v4_relat_1('#skF_6', A_11) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_14, c_611])).
% 3.17/1.40  tff(c_625, plain, (![A_151]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), A_151) | ~v4_relat_1('#skF_6', A_151))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_615])).
% 3.17/1.40  tff(c_167, plain, (![A_79, B_80, C_81]: (r2_hidden('#skF_2'(A_79, B_80, C_81), B_80) | ~r2_hidden(A_79, k9_relat_1(C_81, B_80)) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.40  tff(c_38, plain, (![F_35]: (k1_funct_1('#skF_6', F_35)!='#skF_7' | ~r2_hidden(F_35, '#skF_5') | ~m1_subset_1(F_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.17/1.40  tff(c_307, plain, (![A_113, C_114]: (k1_funct_1('#skF_6', '#skF_2'(A_113, '#skF_5', C_114))!='#skF_7' | ~m1_subset_1('#skF_2'(A_113, '#skF_5', C_114), '#skF_3') | ~r2_hidden(A_113, k9_relat_1(C_114, '#skF_5')) | ~v1_relat_1(C_114))), inference(resolution, [status(thm)], [c_167, c_38])).
% 3.17/1.40  tff(c_314, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_231, c_307])).
% 3.17/1.40  tff(c_330, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_314])).
% 3.17/1.40  tff(c_334, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_330])).
% 3.17/1.40  tff(c_628, plain, (~v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_625, c_334])).
% 3.17/1.40  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_628])).
% 3.17/1.40  tff(c_648, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_330])).
% 3.17/1.40  tff(c_789, plain, (![C_180, A_181, B_182]: (k1_funct_1(C_180, '#skF_2'(A_181, B_182, C_180))=A_181 | ~v1_funct_1(C_180) | ~r2_hidden(A_181, k9_relat_1(C_180, B_182)) | ~v1_relat_1(C_180))), inference(resolution, [status(thm)], [c_273, c_28])).
% 3.17/1.40  tff(c_800, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_231, c_789])).
% 3.17/1.40  tff(c_815, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_46, c_800])).
% 3.17/1.40  tff(c_817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_648, c_815])).
% 3.17/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.40  
% 3.17/1.40  Inference rules
% 3.17/1.40  ----------------------
% 3.17/1.40  #Ref     : 0
% 3.17/1.40  #Sup     : 164
% 3.17/1.40  #Fact    : 0
% 3.17/1.40  #Define  : 0
% 3.17/1.40  #Split   : 6
% 3.17/1.40  #Chain   : 0
% 3.17/1.40  #Close   : 0
% 3.17/1.40  
% 3.17/1.40  Ordering : KBO
% 3.17/1.40  
% 3.17/1.40  Simplification rules
% 3.17/1.40  ----------------------
% 3.17/1.40  #Subsume      : 10
% 3.17/1.40  #Demod        : 28
% 3.17/1.40  #Tautology    : 14
% 3.17/1.40  #SimpNegUnit  : 1
% 3.17/1.40  #BackRed      : 3
% 3.17/1.41  
% 3.17/1.41  #Partial instantiations: 0
% 3.17/1.41  #Strategies tried      : 1
% 3.17/1.41  
% 3.17/1.41  Timing (in seconds)
% 3.17/1.41  ----------------------
% 3.17/1.41  Preprocessing        : 0.33
% 3.17/1.41  Parsing              : 0.18
% 3.17/1.41  CNF conversion       : 0.02
% 3.17/1.41  Main loop            : 0.40
% 3.17/1.41  Inferencing          : 0.15
% 3.17/1.41  Reduction            : 0.11
% 3.17/1.42  Demodulation         : 0.08
% 3.17/1.42  BG Simplification    : 0.02
% 3.17/1.42  Subsumption          : 0.09
% 3.17/1.42  Abstraction          : 0.02
% 3.17/1.42  MUC search           : 0.00
% 3.17/1.42  Cooper               : 0.00
% 3.17/1.42  Total                : 0.80
% 3.17/1.42  Index Insertion      : 0.00
% 3.17/1.42  Index Deletion       : 0.00
% 3.17/1.42  Index Matching       : 0.00
% 3.17/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
