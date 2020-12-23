%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:35 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 223 expanded)
%              Number of leaves         :   34 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 560 expanded)
%              Number of equality atoms :   17 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_75,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_84,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_160,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_167,plain,(
    ! [D_89] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_89) = k9_relat_1('#skF_5',D_89) ),
    inference(resolution,[status(thm)],[c_40,c_160])).

tff(c_38,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_169,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_38])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15),k1_relat_1(C_15))
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_209,plain,(
    ! [A_101,B_102,C_103] :
      ( r2_hidden(k4_tarski('#skF_1'(A_101,B_102,C_103),A_101),C_103)
      | ~ r2_hidden(A_101,k9_relat_1(C_103,B_102))
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_254,plain,(
    ! [C_106,A_107,B_108] :
      ( k1_funct_1(C_106,'#skF_1'(A_107,B_108,C_106)) = A_107
      | ~ v1_funct_1(C_106)
      | ~ r2_hidden(A_107,k9_relat_1(C_106,B_108))
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_209,c_26])).

tff(c_262,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_254])).

tff(c_270,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_262])).

tff(c_24,plain,(
    ! [A_19,C_21] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1(C_21,A_19)),C_21)
      | ~ r2_hidden(A_19,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_291,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_24])).

tff(c_295,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_291])).

tff(c_297,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_300,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_297])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_169,c_300])).

tff(c_306,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [A_61,C_62,B_63] :
      ( m1_subset_1(A_61,C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [A_61,B_2,A_1] :
      ( m1_subset_1(A_61,B_2)
      | ~ r2_hidden(A_61,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_332,plain,(
    ! [B_113] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),B_113)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_113) ) ),
    inference(resolution,[status(thm)],[c_306,c_132])).

tff(c_336,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),A_9)
      | ~ v4_relat_1('#skF_5',A_9)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_332])).

tff(c_340,plain,(
    ! [A_114] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),A_114)
      | ~ v4_relat_1('#skF_5',A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_336])).

tff(c_149,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_1'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden(A_77,k9_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_5',F_33) != '#skF_6'
      | ~ r2_hidden(F_33,'#skF_4')
      | ~ m1_subset_1(F_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_196,plain,(
    ! [A_99,C_100] :
      ( k1_funct_1('#skF_5','#skF_1'(A_99,'#skF_4',C_100)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_99,'#skF_4',C_100),'#skF_2')
      | ~ r2_hidden(A_99,k9_relat_1(C_100,'#skF_4'))
      | ~ v1_relat_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_149,c_36])).

tff(c_199,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_196])).

tff(c_206,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_199])).

tff(c_208,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_343,plain,(
    ~ v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_340,c_208])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_343])).

tff(c_370,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_372,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_hidden(k4_tarski('#skF_1'(A_115,B_116,C_117),A_115),C_117)
      | ~ r2_hidden(A_115,k9_relat_1(C_117,B_116))
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_418,plain,(
    ! [C_120,A_121,B_122] :
      ( k1_funct_1(C_120,'#skF_1'(A_121,B_122,C_120)) = A_121
      | ~ v1_funct_1(C_120)
      | ~ r2_hidden(A_121,k9_relat_1(C_120,B_122))
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_372,c_26])).

tff(c_426,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_418])).

tff(c_434,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_426])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:39:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.65/1.38  
% 2.65/1.38  %Foreground sorts:
% 2.65/1.38  
% 2.65/1.38  
% 2.65/1.38  %Background operators:
% 2.65/1.38  
% 2.65/1.38  
% 2.65/1.38  %Foreground operators:
% 2.65/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.65/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.65/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.65/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.65/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.65/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.65/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.38  
% 2.65/1.40  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 2.65/1.40  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.65/1.40  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.65/1.40  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.65/1.40  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.65/1.40  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.65/1.40  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.65/1.40  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.65/1.40  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.65/1.40  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.65/1.40  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.40  tff(c_75, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.65/1.40  tff(c_84, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_75])).
% 2.65/1.40  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.65/1.40  tff(c_56, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.65/1.40  tff(c_62, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.65/1.40  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62])).
% 2.65/1.40  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.65/1.40  tff(c_160, plain, (![A_86, B_87, C_88, D_89]: (k7_relset_1(A_86, B_87, C_88, D_89)=k9_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.40  tff(c_167, plain, (![D_89]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_89)=k9_relat_1('#skF_5', D_89))), inference(resolution, [status(thm)], [c_40, c_160])).
% 2.65/1.40  tff(c_38, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.40  tff(c_169, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_38])).
% 2.65/1.40  tff(c_22, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_1'(A_13, B_14, C_15), k1_relat_1(C_15)) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.40  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.40  tff(c_209, plain, (![A_101, B_102, C_103]: (r2_hidden(k4_tarski('#skF_1'(A_101, B_102, C_103), A_101), C_103) | ~r2_hidden(A_101, k9_relat_1(C_103, B_102)) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.40  tff(c_26, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.65/1.40  tff(c_254, plain, (![C_106, A_107, B_108]: (k1_funct_1(C_106, '#skF_1'(A_107, B_108, C_106))=A_107 | ~v1_funct_1(C_106) | ~r2_hidden(A_107, k9_relat_1(C_106, B_108)) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_209, c_26])).
% 2.65/1.40  tff(c_262, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_254])).
% 2.65/1.40  tff(c_270, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_262])).
% 2.65/1.40  tff(c_24, plain, (![A_19, C_21]: (r2_hidden(k4_tarski(A_19, k1_funct_1(C_21, A_19)), C_21) | ~r2_hidden(A_19, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.65/1.40  tff(c_291, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_270, c_24])).
% 2.65/1.40  tff(c_295, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_291])).
% 2.65/1.40  tff(c_297, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_295])).
% 2.65/1.40  tff(c_300, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_297])).
% 2.65/1.40  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_169, c_300])).
% 2.65/1.40  tff(c_306, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_295])).
% 2.65/1.40  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.40  tff(c_127, plain, (![A_61, C_62, B_63]: (m1_subset_1(A_61, C_62) | ~m1_subset_1(B_63, k1_zfmisc_1(C_62)) | ~r2_hidden(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.40  tff(c_132, plain, (![A_61, B_2, A_1]: (m1_subset_1(A_61, B_2) | ~r2_hidden(A_61, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_127])).
% 2.65/1.40  tff(c_332, plain, (![B_113]: (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), B_113) | ~r1_tarski(k1_relat_1('#skF_5'), B_113))), inference(resolution, [status(thm)], [c_306, c_132])).
% 2.65/1.40  tff(c_336, plain, (![A_9]: (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), A_9) | ~v4_relat_1('#skF_5', A_9) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_332])).
% 2.65/1.40  tff(c_340, plain, (![A_114]: (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), A_114) | ~v4_relat_1('#skF_5', A_114))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_336])).
% 2.65/1.40  tff(c_149, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_1'(A_77, B_78, C_79), B_78) | ~r2_hidden(A_77, k9_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.40  tff(c_36, plain, (![F_33]: (k1_funct_1('#skF_5', F_33)!='#skF_6' | ~r2_hidden(F_33, '#skF_4') | ~m1_subset_1(F_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.40  tff(c_196, plain, (![A_99, C_100]: (k1_funct_1('#skF_5', '#skF_1'(A_99, '#skF_4', C_100))!='#skF_6' | ~m1_subset_1('#skF_1'(A_99, '#skF_4', C_100), '#skF_2') | ~r2_hidden(A_99, k9_relat_1(C_100, '#skF_4')) | ~v1_relat_1(C_100))), inference(resolution, [status(thm)], [c_149, c_36])).
% 2.65/1.40  tff(c_199, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_196])).
% 2.65/1.40  tff(c_206, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_199])).
% 2.65/1.40  tff(c_208, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_206])).
% 2.65/1.40  tff(c_343, plain, (~v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_340, c_208])).
% 2.65/1.40  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_343])).
% 2.65/1.40  tff(c_370, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_206])).
% 2.65/1.40  tff(c_372, plain, (![A_115, B_116, C_117]: (r2_hidden(k4_tarski('#skF_1'(A_115, B_116, C_117), A_115), C_117) | ~r2_hidden(A_115, k9_relat_1(C_117, B_116)) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.40  tff(c_418, plain, (![C_120, A_121, B_122]: (k1_funct_1(C_120, '#skF_1'(A_121, B_122, C_120))=A_121 | ~v1_funct_1(C_120) | ~r2_hidden(A_121, k9_relat_1(C_120, B_122)) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_372, c_26])).
% 2.65/1.40  tff(c_426, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_418])).
% 2.65/1.40  tff(c_434, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_426])).
% 2.65/1.40  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_434])).
% 2.65/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.40  
% 2.65/1.40  Inference rules
% 2.65/1.40  ----------------------
% 2.65/1.40  #Ref     : 0
% 2.65/1.40  #Sup     : 82
% 2.65/1.40  #Fact    : 0
% 2.65/1.40  #Define  : 0
% 2.65/1.40  #Split   : 5
% 2.65/1.40  #Chain   : 0
% 2.65/1.40  #Close   : 0
% 2.65/1.40  
% 2.65/1.40  Ordering : KBO
% 2.65/1.40  
% 2.65/1.40  Simplification rules
% 2.65/1.40  ----------------------
% 2.65/1.40  #Subsume      : 3
% 2.65/1.40  #Demod        : 26
% 2.65/1.40  #Tautology    : 16
% 2.65/1.40  #SimpNegUnit  : 1
% 2.65/1.40  #BackRed      : 2
% 2.65/1.40  
% 2.65/1.40  #Partial instantiations: 0
% 2.65/1.40  #Strategies tried      : 1
% 2.65/1.40  
% 2.65/1.40  Timing (in seconds)
% 2.65/1.40  ----------------------
% 2.65/1.40  Preprocessing        : 0.33
% 2.65/1.40  Parsing              : 0.18
% 2.65/1.40  CNF conversion       : 0.02
% 2.65/1.40  Main loop            : 0.28
% 2.65/1.40  Inferencing          : 0.11
% 2.65/1.40  Reduction            : 0.08
% 2.65/1.40  Demodulation         : 0.06
% 2.65/1.40  BG Simplification    : 0.02
% 2.65/1.40  Subsumption          : 0.05
% 2.65/1.40  Abstraction          : 0.02
% 2.65/1.40  MUC search           : 0.00
% 2.65/1.40  Cooper               : 0.00
% 2.65/1.40  Total                : 0.64
% 2.65/1.40  Index Insertion      : 0.00
% 2.65/1.40  Index Deletion       : 0.00
% 2.65/1.40  Index Matching       : 0.00
% 2.65/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
