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
% DateTime   : Thu Dec  3 10:16:27 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 273 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 705 expanded)
%              Number of equality atoms :   11 (  89 expanded)
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

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

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
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_14,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_158,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k7_relset_1(A_84,B_85,C_86,D_87) = k9_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_165,plain,(
    ! [D_87] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_87) = k9_relat_1('#skF_5',D_87) ),
    inference(resolution,[status(thm)],[c_40,c_158])).

tff(c_38,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_168,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_38])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden('#skF_1'(A_14,B_15,C_16),B_15)
      | ~ r2_hidden(A_14,k9_relat_1(C_16,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_84,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_202,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(k4_tarski('#skF_1'(A_100,B_101,C_102),A_100),C_102)
      | ~ r2_hidden(A_100,k9_relat_1(C_102,B_101))
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [C_22,A_20,B_21] :
      ( k1_funct_1(C_22,A_20) = B_21
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_237,plain,(
    ! [C_105,A_106,B_107] :
      ( k1_funct_1(C_105,'#skF_1'(A_106,B_107,C_105)) = A_106
      | ~ v1_funct_1(C_105)
      | ~ r2_hidden(A_106,k9_relat_1(C_105,B_107))
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_202,c_26])).

tff(c_245,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_168,c_237])).

tff(c_253,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_245])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden('#skF_1'(A_14,B_15,C_16),k1_relat_1(C_16))
      | ~ r2_hidden(A_14,k9_relat_1(C_16,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_20,C_22] :
      ( r2_hidden(k4_tarski(A_20,k1_funct_1(C_22,A_20)),C_22)
      | ~ r2_hidden(A_20,k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_258,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_24])).

tff(c_262,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_258])).

tff(c_264,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_283,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_264])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_168,c_283])).

tff(c_289,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_308,plain,(
    ! [A_112] :
      ( r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),A_112)
      | ~ m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1(A_112)) ) ),
    inference(resolution,[status(thm)],[c_289,c_2])).

tff(c_314,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),B_113)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_113) ) ),
    inference(resolution,[status(thm)],[c_6,c_308])).

tff(c_36,plain,(
    ! [F_34] :
      ( k1_funct_1('#skF_5',F_34) != '#skF_6'
      | ~ r2_hidden(F_34,'#skF_4')
      | ~ r2_hidden(F_34,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_323,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_314,c_36])).

tff(c_328,plain,
    ( ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_323])).

tff(c_329,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_332,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_329])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_84,c_332])).

tff(c_337,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_354,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_337])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_168,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.19/1.30  
% 2.19/1.30  %Foreground sorts:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Background operators:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Foreground operators:
% 2.19/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.19/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.19/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.19/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.30  
% 2.47/1.31  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.47/1.31  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.47/1.31  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.47/1.31  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.47/1.31  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.47/1.31  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.47/1.31  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.47/1.31  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.47/1.31  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.47/1.31  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.47/1.31  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.31  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.31  tff(c_56, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.31  tff(c_62, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.47/1.31  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62])).
% 2.47/1.31  tff(c_158, plain, (![A_84, B_85, C_86, D_87]: (k7_relset_1(A_84, B_85, C_86, D_87)=k9_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.31  tff(c_165, plain, (![D_87]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_87)=k9_relat_1('#skF_5', D_87))), inference(resolution, [status(thm)], [c_40, c_158])).
% 2.47/1.31  tff(c_38, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.31  tff(c_168, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_38])).
% 2.47/1.31  tff(c_18, plain, (![A_14, B_15, C_16]: (r2_hidden('#skF_1'(A_14, B_15, C_16), B_15) | ~r2_hidden(A_14, k9_relat_1(C_16, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.31  tff(c_75, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.31  tff(c_84, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_75])).
% 2.47/1.31  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.31  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.31  tff(c_202, plain, (![A_100, B_101, C_102]: (r2_hidden(k4_tarski('#skF_1'(A_100, B_101, C_102), A_100), C_102) | ~r2_hidden(A_100, k9_relat_1(C_102, B_101)) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.31  tff(c_26, plain, (![C_22, A_20, B_21]: (k1_funct_1(C_22, A_20)=B_21 | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.31  tff(c_237, plain, (![C_105, A_106, B_107]: (k1_funct_1(C_105, '#skF_1'(A_106, B_107, C_105))=A_106 | ~v1_funct_1(C_105) | ~r2_hidden(A_106, k9_relat_1(C_105, B_107)) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_202, c_26])).
% 2.47/1.31  tff(c_245, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_168, c_237])).
% 2.47/1.31  tff(c_253, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_245])).
% 2.47/1.31  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.47/1.31  tff(c_22, plain, (![A_14, B_15, C_16]: (r2_hidden('#skF_1'(A_14, B_15, C_16), k1_relat_1(C_16)) | ~r2_hidden(A_14, k9_relat_1(C_16, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.31  tff(c_24, plain, (![A_20, C_22]: (r2_hidden(k4_tarski(A_20, k1_funct_1(C_22, A_20)), C_22) | ~r2_hidden(A_20, k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.31  tff(c_258, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_253, c_24])).
% 2.47/1.31  tff(c_262, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_258])).
% 2.47/1.31  tff(c_264, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_262])).
% 2.47/1.31  tff(c_283, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_264])).
% 2.47/1.31  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_168, c_283])).
% 2.47/1.31  tff(c_289, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_262])).
% 2.47/1.31  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.31  tff(c_308, plain, (![A_112]: (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), A_112) | ~m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1(A_112)))), inference(resolution, [status(thm)], [c_289, c_2])).
% 2.47/1.31  tff(c_314, plain, (![B_113]: (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), B_113) | ~r1_tarski(k1_relat_1('#skF_5'), B_113))), inference(resolution, [status(thm)], [c_6, c_308])).
% 2.47/1.31  tff(c_36, plain, (![F_34]: (k1_funct_1('#skF_5', F_34)!='#skF_6' | ~r2_hidden(F_34, '#skF_4') | ~r2_hidden(F_34, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.31  tff(c_323, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_314, c_36])).
% 2.47/1.31  tff(c_328, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_323])).
% 2.47/1.31  tff(c_329, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_328])).
% 2.47/1.31  tff(c_332, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_329])).
% 2.47/1.31  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_84, c_332])).
% 2.47/1.31  tff(c_337, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_328])).
% 2.47/1.31  tff(c_354, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_337])).
% 2.47/1.31  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_168, c_354])).
% 2.47/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.31  
% 2.47/1.31  Inference rules
% 2.47/1.31  ----------------------
% 2.47/1.31  #Ref     : 0
% 2.47/1.31  #Sup     : 63
% 2.47/1.31  #Fact    : 0
% 2.47/1.31  #Define  : 0
% 2.47/1.31  #Split   : 3
% 2.47/1.31  #Chain   : 0
% 2.47/1.31  #Close   : 0
% 2.47/1.31  
% 2.47/1.31  Ordering : KBO
% 2.47/1.31  
% 2.47/1.31  Simplification rules
% 2.47/1.31  ----------------------
% 2.47/1.31  #Subsume      : 6
% 2.47/1.31  #Demod        : 29
% 2.47/1.31  #Tautology    : 15
% 2.47/1.31  #SimpNegUnit  : 0
% 2.47/1.31  #BackRed      : 3
% 2.47/1.31  
% 2.47/1.31  #Partial instantiations: 0
% 2.47/1.31  #Strategies tried      : 1
% 2.47/1.31  
% 2.47/1.31  Timing (in seconds)
% 2.47/1.31  ----------------------
% 2.47/1.31  Preprocessing        : 0.32
% 2.47/1.31  Parsing              : 0.17
% 2.47/1.31  CNF conversion       : 0.02
% 2.47/1.31  Main loop            : 0.23
% 2.47/1.32  Inferencing          : 0.09
% 2.47/1.32  Reduction            : 0.07
% 2.47/1.32  Demodulation         : 0.05
% 2.47/1.32  BG Simplification    : 0.01
% 2.47/1.32  Subsumption          : 0.04
% 2.47/1.32  Abstraction          : 0.02
% 2.47/1.32  MUC search           : 0.00
% 2.47/1.32  Cooper               : 0.00
% 2.47/1.32  Total                : 0.59
% 2.47/1.32  Index Insertion      : 0.00
% 2.47/1.32  Index Deletion       : 0.00
% 2.47/1.32  Index Matching       : 0.00
% 2.47/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
