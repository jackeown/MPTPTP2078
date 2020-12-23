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
% DateTime   : Thu Dec  3 09:56:34 EST 2020

% Result     : Theorem 9.56s
% Output     : CNFRefutation 9.74s
% Verified   : 
% Statistics : Number of formulae       :   79 (  94 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 152 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_80,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_140,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_152,plain,(
    ! [A_63] : r1_tarski(A_63,A_63) ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    ! [A_36] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_21] : k2_subset_1(A_21) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_subset_1(A_27)) = k2_subset_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_53,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_subset_1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38])).

tff(c_55,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_xboole_0) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_53])).

tff(c_16,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_326,plain,(
    ! [C_93,A_94,B_95] :
      ( r1_tarski(C_93,k3_subset_1(A_94,B_95))
      | ~ r1_tarski(B_95,k3_subset_1(A_94,C_93))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_346,plain,(
    ! [C_93,A_94] :
      ( r1_tarski(C_93,k3_subset_1(A_94,k1_xboole_0))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_16,c_326])).

tff(c_357,plain,(
    ! [C_96,A_97] :
      ( r1_tarski(C_96,A_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_97)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_55,c_346])).

tff(c_385,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_357])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_434,plain,(
    ! [A_100] :
      ( r1_tarski(A_100,'#skF_3')
      | ~ r1_tarski(A_100,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_385,c_14])).

tff(c_9799,plain,(
    ! [A_441,A_442] :
      ( r1_tarski(A_441,'#skF_3')
      | ~ r1_tarski(A_441,A_442)
      | ~ r1_tarski(A_442,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_434,c_14])).

tff(c_9899,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k3_xboole_0(A_10,B_11),'#skF_3')
      | ~ r1_tarski(A_10,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_9799])).

tff(c_34,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [A_22] : m1_subset_1(k2_subset_1(A_22),k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_22] : m1_subset_1(A_22,k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_zfmisc_1(A_16),k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_160,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10164,plain,(
    ! [B_466,B_467,A_468] :
      ( r2_hidden(B_466,B_467)
      | ~ r1_tarski(A_468,B_467)
      | ~ m1_subset_1(B_466,A_468)
      | v1_xboole_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_22,c_160])).

tff(c_10224,plain,(
    ! [B_466,B_17,A_16] :
      ( r2_hidden(B_466,k1_zfmisc_1(B_17))
      | ~ m1_subset_1(B_466,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_10164])).

tff(c_13452,plain,(
    ! [B_593,B_594,A_595] :
      ( r2_hidden(B_593,k1_zfmisc_1(B_594))
      | ~ m1_subset_1(B_593,k1_zfmisc_1(A_595))
      | ~ r1_tarski(A_595,B_594) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_10224])).

tff(c_13501,plain,(
    ! [A_597,B_598] :
      ( r2_hidden(A_597,k1_zfmisc_1(B_598))
      | ~ r1_tarski(A_597,B_598) ) ),
    inference(resolution,[status(thm)],[c_54,c_13452])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ r2_hidden(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13506,plain,(
    ! [A_597,B_598] :
      ( m1_subset_1(A_597,k1_zfmisc_1(B_598))
      | v1_xboole_0(k1_zfmisc_1(B_598))
      | ~ r1_tarski(A_597,B_598) ) ),
    inference(resolution,[status(thm)],[c_13501,c_20])).

tff(c_14836,plain,(
    ! [A_630,B_631] :
      ( m1_subset_1(A_630,k1_zfmisc_1(B_631))
      | ~ r1_tarski(A_630,B_631) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_13506])).

tff(c_486,plain,(
    ! [A_102,C_103,B_104] :
      ( r1_tarski(k3_subset_1(A_102,C_103),k3_subset_1(A_102,B_104))
      | ~ r1_tarski(B_104,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_243,plain,(
    ! [A_81,B_82,C_83] :
      ( k9_subset_1(A_81,B_82,C_83) = k3_xboole_0(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_262,plain,(
    ! [B_82] : k9_subset_1('#skF_3',B_82,'#skF_5') = k3_xboole_0(B_82,'#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_243])).

tff(c_48,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_266,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_48])).

tff(c_489,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_486,c_266])).

tff(c_502,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12,c_489])).

tff(c_14885,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_14836,c_502])).

tff(c_14891,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_9899,c_14885])).

tff(c_14904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_14891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n006.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 20:13:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.56/3.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.54  
% 9.74/3.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.54  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 9.74/3.54  
% 9.74/3.54  %Foreground sorts:
% 9.74/3.54  
% 9.74/3.54  
% 9.74/3.54  %Background operators:
% 9.74/3.54  
% 9.74/3.54  
% 9.74/3.54  %Foreground operators:
% 9.74/3.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.74/3.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.74/3.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.74/3.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.74/3.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.74/3.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.74/3.54  tff('#skF_5', type, '#skF_5': $i).
% 9.74/3.54  tff('#skF_3', type, '#skF_3': $i).
% 9.74/3.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.74/3.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.74/3.54  tff('#skF_4', type, '#skF_4': $i).
% 9.74/3.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.74/3.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.74/3.54  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 9.74/3.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.74/3.54  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.74/3.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.74/3.54  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.74/3.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.74/3.54  
% 9.74/3.56  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.74/3.56  tff(f_40, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.74/3.56  tff(f_108, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 9.74/3.56  tff(f_100, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.74/3.56  tff(f_67, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 9.74/3.56  tff(f_69, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.74/3.56  tff(f_80, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 9.74/3.56  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.74/3.56  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 9.74/3.56  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.74/3.56  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.74/3.56  tff(f_71, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.74/3.56  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 9.74/3.56  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.74/3.56  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 9.74/3.56  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.74/3.56  tff(c_140, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.74/3.56  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.74/3.56  tff(c_152, plain, (![A_63]: (r1_tarski(A_63, A_63))), inference(resolution, [status(thm)], [c_140, c_8])).
% 9.74/3.56  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.74/3.56  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.74/3.56  tff(c_46, plain, (![A_36]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.74/3.56  tff(c_28, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.74/3.56  tff(c_30, plain, (![A_21]: (k2_subset_1(A_21)=A_21)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.74/3.56  tff(c_38, plain, (![A_27]: (k3_subset_1(A_27, k1_subset_1(A_27))=k2_subset_1(A_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.74/3.56  tff(c_53, plain, (![A_27]: (k3_subset_1(A_27, k1_subset_1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38])).
% 9.74/3.56  tff(c_55, plain, (![A_27]: (k3_subset_1(A_27, k1_xboole_0)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_53])).
% 9.74/3.56  tff(c_16, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.74/3.56  tff(c_326, plain, (![C_93, A_94, B_95]: (r1_tarski(C_93, k3_subset_1(A_94, B_95)) | ~r1_tarski(B_95, k3_subset_1(A_94, C_93)) | ~m1_subset_1(C_93, k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.74/3.56  tff(c_346, plain, (![C_93, A_94]: (r1_tarski(C_93, k3_subset_1(A_94, k1_xboole_0)) | ~m1_subset_1(C_93, k1_zfmisc_1(A_94)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_16, c_326])).
% 9.74/3.56  tff(c_357, plain, (![C_96, A_97]: (r1_tarski(C_96, A_97) | ~m1_subset_1(C_96, k1_zfmisc_1(A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_55, c_346])).
% 9.74/3.56  tff(c_385, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_357])).
% 9.74/3.56  tff(c_14, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, C_14) | ~r1_tarski(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.74/3.56  tff(c_434, plain, (![A_100]: (r1_tarski(A_100, '#skF_3') | ~r1_tarski(A_100, '#skF_4'))), inference(resolution, [status(thm)], [c_385, c_14])).
% 9.74/3.56  tff(c_9799, plain, (![A_441, A_442]: (r1_tarski(A_441, '#skF_3') | ~r1_tarski(A_441, A_442) | ~r1_tarski(A_442, '#skF_4'))), inference(resolution, [status(thm)], [c_434, c_14])).
% 9.74/3.56  tff(c_9899, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), '#skF_3') | ~r1_tarski(A_10, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_9799])).
% 9.74/3.56  tff(c_34, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.74/3.56  tff(c_32, plain, (![A_22]: (m1_subset_1(k2_subset_1(A_22), k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.74/3.56  tff(c_54, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 9.74/3.56  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k1_zfmisc_1(A_16), k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.74/3.56  tff(c_22, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.74/3.56  tff(c_160, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.74/3.56  tff(c_10164, plain, (![B_466, B_467, A_468]: (r2_hidden(B_466, B_467) | ~r1_tarski(A_468, B_467) | ~m1_subset_1(B_466, A_468) | v1_xboole_0(A_468))), inference(resolution, [status(thm)], [c_22, c_160])).
% 9.74/3.56  tff(c_10224, plain, (![B_466, B_17, A_16]: (r2_hidden(B_466, k1_zfmisc_1(B_17)) | ~m1_subset_1(B_466, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)) | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_18, c_10164])).
% 9.74/3.56  tff(c_13452, plain, (![B_593, B_594, A_595]: (r2_hidden(B_593, k1_zfmisc_1(B_594)) | ~m1_subset_1(B_593, k1_zfmisc_1(A_595)) | ~r1_tarski(A_595, B_594))), inference(negUnitSimplification, [status(thm)], [c_34, c_10224])).
% 9.74/3.56  tff(c_13501, plain, (![A_597, B_598]: (r2_hidden(A_597, k1_zfmisc_1(B_598)) | ~r1_tarski(A_597, B_598))), inference(resolution, [status(thm)], [c_54, c_13452])).
% 9.74/3.56  tff(c_20, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~r2_hidden(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.74/3.56  tff(c_13506, plain, (![A_597, B_598]: (m1_subset_1(A_597, k1_zfmisc_1(B_598)) | v1_xboole_0(k1_zfmisc_1(B_598)) | ~r1_tarski(A_597, B_598))), inference(resolution, [status(thm)], [c_13501, c_20])).
% 9.74/3.56  tff(c_14836, plain, (![A_630, B_631]: (m1_subset_1(A_630, k1_zfmisc_1(B_631)) | ~r1_tarski(A_630, B_631))), inference(negUnitSimplification, [status(thm)], [c_34, c_13506])).
% 9.74/3.56  tff(c_486, plain, (![A_102, C_103, B_104]: (r1_tarski(k3_subset_1(A_102, C_103), k3_subset_1(A_102, B_104)) | ~r1_tarski(B_104, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(A_102)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.74/3.56  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.74/3.56  tff(c_243, plain, (![A_81, B_82, C_83]: (k9_subset_1(A_81, B_82, C_83)=k3_xboole_0(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.74/3.56  tff(c_262, plain, (![B_82]: (k9_subset_1('#skF_3', B_82, '#skF_5')=k3_xboole_0(B_82, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_243])).
% 9.74/3.56  tff(c_48, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.74/3.56  tff(c_266, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_48])).
% 9.74/3.56  tff(c_489, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_486, c_266])).
% 9.74/3.56  tff(c_502, plain, (~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12, c_489])).
% 9.74/3.56  tff(c_14885, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_14836, c_502])).
% 9.74/3.56  tff(c_14891, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_9899, c_14885])).
% 9.74/3.56  tff(c_14904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_14891])).
% 9.74/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.56  
% 9.74/3.56  Inference rules
% 9.74/3.56  ----------------------
% 9.74/3.56  #Ref     : 0
% 9.74/3.56  #Sup     : 3403
% 9.74/3.56  #Fact    : 0
% 9.74/3.56  #Define  : 0
% 9.74/3.56  #Split   : 18
% 9.74/3.56  #Chain   : 0
% 9.74/3.56  #Close   : 0
% 9.74/3.56  
% 9.74/3.56  Ordering : KBO
% 9.74/3.56  
% 9.74/3.56  Simplification rules
% 9.74/3.56  ----------------------
% 9.74/3.56  #Subsume      : 652
% 9.74/3.56  #Demod        : 1117
% 9.74/3.56  #Tautology    : 1069
% 9.74/3.56  #SimpNegUnit  : 211
% 9.74/3.56  #BackRed      : 92
% 9.74/3.56  
% 9.74/3.56  #Partial instantiations: 0
% 9.74/3.56  #Strategies tried      : 1
% 9.74/3.56  
% 9.74/3.56  Timing (in seconds)
% 9.74/3.56  ----------------------
% 9.74/3.56  Preprocessing        : 0.35
% 9.85/3.56  Parsing              : 0.19
% 9.85/3.56  CNF conversion       : 0.03
% 9.85/3.56  Main loop            : 2.44
% 9.85/3.56  Inferencing          : 0.61
% 9.85/3.56  Reduction            : 0.99
% 9.85/3.56  Demodulation         : 0.77
% 9.85/3.56  BG Simplification    : 0.06
% 9.85/3.56  Subsumption          : 0.59
% 9.85/3.56  Abstraction          : 0.08
% 9.85/3.56  MUC search           : 0.00
% 9.85/3.56  Cooper               : 0.00
% 9.85/3.56  Total                : 2.83
% 9.85/3.56  Index Insertion      : 0.00
% 9.85/3.56  Index Deletion       : 0.00
% 9.85/3.56  Index Matching       : 0.00
% 9.85/3.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
