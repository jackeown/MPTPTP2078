%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:26 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 131 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 222 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_47,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_37,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_45,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_37])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_312,plain,(
    ! [A_105,B_106,B_107] :
      ( r2_hidden('#skF_1'(A_105,B_106),B_107)
      | ~ r1_tarski(A_105,B_107)
      | r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_517,plain,(
    ! [A_181,B_182,B_183,B_184] :
      ( r2_hidden('#skF_1'(A_181,B_182),B_183)
      | ~ r1_tarski(B_184,B_183)
      | ~ r1_tarski(A_181,B_184)
      | r1_tarski(A_181,B_182) ) ),
    inference(resolution,[status(thm)],[c_312,c_2])).

tff(c_580,plain,(
    ! [A_190,B_191] :
      ( r2_hidden('#skF_1'(A_190,B_191),k2_zfmisc_1('#skF_2','#skF_4'))
      | ~ r1_tarski(A_190,'#skF_5')
      | r1_tarski(A_190,B_191) ) ),
    inference(resolution,[status(thm)],[c_45,c_517])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_589,plain,(
    ! [A_192] :
      ( ~ r1_tarski(A_192,'#skF_5')
      | r1_tarski(A_192,k2_zfmisc_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_580,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_183,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_191,plain,(
    ! [A_6,B_72,A_73] :
      ( v5_relat_1(A_6,B_72)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_73,B_72)) ) ),
    inference(resolution,[status(thm)],[c_10,c_183])).

tff(c_664,plain,(
    ! [A_199] :
      ( v5_relat_1(A_199,'#skF_4')
      | ~ r1_tarski(A_199,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_589,c_191])).

tff(c_78,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [A_48,B_49] :
      ( v1_relat_1(A_48)
      | ~ v1_relat_1(B_49)
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_10,c_78])).

tff(c_101,plain,(
    ! [B_16,A_15] :
      ( v1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_88])).

tff(c_30,plain,(
    ! [C_29,A_27,B_28] :
      ( m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ r1_tarski(k2_relat_1(C_29),B_28)
      | ~ r1_tarski(k1_relat_1(C_29),A_27)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_195,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k5_relset_1(A_79,B_80,C_81,D_82) = k7_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_202,plain,(
    ! [D_82] : k5_relset_1('#skF_2','#skF_4','#skF_5',D_82) = k7_relat_1('#skF_5',D_82) ),
    inference(resolution,[status(thm)],[c_34,c_195])).

tff(c_32,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_234,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_32])).

tff(c_276,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_234])).

tff(c_280,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_283,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_280])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_283])).

tff(c_289,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_288,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_340,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_343,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_340])).

tff(c_346,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_343])).

tff(c_670,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_664,c_346])).

tff(c_690,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_670])).

tff(c_694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_690])).

tff(c_695,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_699,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_695])).

tff(c_703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.47  
% 2.90/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.47  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.90/1.47  
% 2.90/1.47  %Foreground sorts:
% 2.90/1.47  
% 2.90/1.47  
% 2.90/1.47  %Background operators:
% 2.90/1.47  
% 2.90/1.47  
% 2.90/1.47  %Foreground operators:
% 2.90/1.47  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.90/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.90/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.90/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.90/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.47  
% 2.90/1.49  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.90/1.49  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.90/1.49  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.90/1.49  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.90/1.49  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.90/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.90/1.49  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.49  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.90/1.49  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.90/1.49  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.90/1.49  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.90/1.49  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.90/1.49  tff(c_47, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.49  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_47])).
% 2.90/1.49  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.90/1.49  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.49  tff(c_37, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.90/1.49  tff(c_45, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_37])).
% 2.90/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.49  tff(c_109, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.49  tff(c_312, plain, (![A_105, B_106, B_107]: (r2_hidden('#skF_1'(A_105, B_106), B_107) | ~r1_tarski(A_105, B_107) | r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_6, c_109])).
% 2.90/1.49  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.49  tff(c_517, plain, (![A_181, B_182, B_183, B_184]: (r2_hidden('#skF_1'(A_181, B_182), B_183) | ~r1_tarski(B_184, B_183) | ~r1_tarski(A_181, B_184) | r1_tarski(A_181, B_182))), inference(resolution, [status(thm)], [c_312, c_2])).
% 2.90/1.49  tff(c_580, plain, (![A_190, B_191]: (r2_hidden('#skF_1'(A_190, B_191), k2_zfmisc_1('#skF_2', '#skF_4')) | ~r1_tarski(A_190, '#skF_5') | r1_tarski(A_190, B_191))), inference(resolution, [status(thm)], [c_45, c_517])).
% 2.90/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.49  tff(c_589, plain, (![A_192]: (~r1_tarski(A_192, '#skF_5') | r1_tarski(A_192, k2_zfmisc_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_580, c_4])).
% 2.90/1.49  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.90/1.49  tff(c_183, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.90/1.49  tff(c_191, plain, (![A_6, B_72, A_73]: (v5_relat_1(A_6, B_72) | ~r1_tarski(A_6, k2_zfmisc_1(A_73, B_72)))), inference(resolution, [status(thm)], [c_10, c_183])).
% 2.90/1.49  tff(c_664, plain, (![A_199]: (v5_relat_1(A_199, '#skF_4') | ~r1_tarski(A_199, '#skF_5'))), inference(resolution, [status(thm)], [c_589, c_191])).
% 2.90/1.49  tff(c_78, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.49  tff(c_88, plain, (![A_48, B_49]: (v1_relat_1(A_48) | ~v1_relat_1(B_49) | ~r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_10, c_78])).
% 2.90/1.49  tff(c_101, plain, (![B_16, A_15]: (v1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_20, c_88])).
% 2.90/1.49  tff(c_30, plain, (![C_29, A_27, B_28]: (m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~r1_tarski(k2_relat_1(C_29), B_28) | ~r1_tarski(k1_relat_1(C_29), A_27) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.90/1.49  tff(c_195, plain, (![A_79, B_80, C_81, D_82]: (k5_relset_1(A_79, B_80, C_81, D_82)=k7_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.49  tff(c_202, plain, (![D_82]: (k5_relset_1('#skF_2', '#skF_4', '#skF_5', D_82)=k7_relat_1('#skF_5', D_82))), inference(resolution, [status(thm)], [c_34, c_195])).
% 2.90/1.49  tff(c_32, plain, (~m1_subset_1(k5_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.90/1.49  tff(c_234, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_32])).
% 2.90/1.49  tff(c_276, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_234])).
% 2.90/1.49  tff(c_280, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_276])).
% 2.90/1.49  tff(c_283, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_101, c_280])).
% 2.90/1.49  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_283])).
% 2.90/1.49  tff(c_289, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_276])).
% 2.90/1.49  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.90/1.49  tff(c_288, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_276])).
% 2.90/1.49  tff(c_340, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_288])).
% 2.90/1.49  tff(c_343, plain, (~v5_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_340])).
% 2.90/1.49  tff(c_346, plain, (~v5_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_343])).
% 2.90/1.49  tff(c_670, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_664, c_346])).
% 2.90/1.49  tff(c_690, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_670])).
% 2.90/1.49  tff(c_694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_690])).
% 2.90/1.49  tff(c_695, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_288])).
% 2.90/1.49  tff(c_699, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_695])).
% 2.90/1.49  tff(c_703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_699])).
% 2.90/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.49  
% 2.90/1.49  Inference rules
% 2.90/1.49  ----------------------
% 2.90/1.49  #Ref     : 0
% 2.90/1.49  #Sup     : 129
% 2.90/1.49  #Fact    : 0
% 2.90/1.49  #Define  : 0
% 2.90/1.49  #Split   : 3
% 2.90/1.49  #Chain   : 0
% 2.90/1.49  #Close   : 0
% 2.90/1.49  
% 2.90/1.49  Ordering : KBO
% 2.90/1.49  
% 2.90/1.49  Simplification rules
% 2.90/1.49  ----------------------
% 2.90/1.49  #Subsume      : 9
% 2.90/1.49  #Demod        : 37
% 2.90/1.49  #Tautology    : 21
% 2.90/1.49  #SimpNegUnit  : 0
% 2.90/1.49  #BackRed      : 2
% 2.90/1.49  
% 2.90/1.49  #Partial instantiations: 0
% 2.90/1.49  #Strategies tried      : 1
% 2.90/1.49  
% 2.90/1.49  Timing (in seconds)
% 2.90/1.49  ----------------------
% 2.90/1.49  Preprocessing        : 0.29
% 2.90/1.49  Parsing              : 0.16
% 2.90/1.49  CNF conversion       : 0.02
% 2.90/1.49  Main loop            : 0.37
% 2.90/1.49  Inferencing          : 0.15
% 2.90/1.49  Reduction            : 0.11
% 2.90/1.49  Demodulation         : 0.07
% 2.90/1.49  BG Simplification    : 0.02
% 2.90/1.49  Subsumption          : 0.06
% 2.90/1.49  Abstraction          : 0.02
% 2.90/1.49  MUC search           : 0.00
% 2.90/1.49  Cooper               : 0.00
% 2.90/1.49  Total                : 0.70
% 2.90/1.49  Index Insertion      : 0.00
% 2.90/1.49  Index Deletion       : 0.00
% 2.90/1.49  Index Matching       : 0.00
% 2.90/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
