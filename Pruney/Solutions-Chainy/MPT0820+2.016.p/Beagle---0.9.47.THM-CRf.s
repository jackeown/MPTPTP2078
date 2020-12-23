%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:02 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 124 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_131,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_140,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_131])).

tff(c_84,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_84])).

tff(c_30,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1204,plain,(
    ! [A_158,B_159] :
      ( r1_tarski(k2_relat_1(A_158),k2_relat_1(B_159))
      | ~ r1_tarski(A_158,B_159)
      | ~ v1_relat_1(B_159)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [A_27,B_28] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_27,B_28)),B_28) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_395,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(A_84,C_85)
      | ~ r1_tarski(B_86,C_85)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_411,plain,(
    ! [A_84,B_28,A_27] :
      ( r1_tarski(A_84,B_28)
      | ~ r1_tarski(A_84,k2_relat_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(resolution,[status(thm)],[c_34,c_395])).

tff(c_1208,plain,(
    ! [A_158,B_28,A_27] :
      ( r1_tarski(k2_relat_1(A_158),B_28)
      | ~ r1_tarski(A_158,k2_zfmisc_1(A_27,B_28))
      | ~ v1_relat_1(k2_zfmisc_1(A_27,B_28))
      | ~ v1_relat_1(A_158) ) ),
    inference(resolution,[status(thm)],[c_1204,c_411])).

tff(c_4013,plain,(
    ! [A_389,B_390,A_391] :
      ( r1_tarski(k2_relat_1(A_389),B_390)
      | ~ r1_tarski(A_389,k2_zfmisc_1(A_391,B_390))
      | ~ v1_relat_1(A_389) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1208])).

tff(c_4099,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_4013])).

tff(c_4172,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_4099])).

tff(c_26,plain,(
    ! [A_20] :
      ( k2_xboole_0(k1_relat_1(A_20),k2_relat_1(A_20)) = k3_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1405,plain,(
    ! [A_181,C_182,B_183,D_184] :
      ( r1_tarski(k2_xboole_0(A_181,C_182),k2_xboole_0(B_183,D_184))
      | ~ r1_tarski(C_182,D_184)
      | ~ r1_tarski(A_181,B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4982,plain,(
    ! [A_411,B_412,D_413] :
      ( r1_tarski(k3_relat_1(A_411),k2_xboole_0(B_412,D_413))
      | ~ r1_tarski(k2_relat_1(A_411),D_413)
      | ~ r1_tarski(k1_relat_1(A_411),B_412)
      | ~ v1_relat_1(A_411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1405])).

tff(c_48,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4994,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4982,c_48])).

tff(c_5019,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_4172,c_4994])).

tff(c_40,plain,(
    ! [A_30,B_32] :
      ( r1_tarski(k1_relat_1(A_30),k1_relat_1(B_32))
      | ~ r1_tarski(A_30,B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [A_25,B_26] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_25,B_26)),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_931,plain,(
    ! [A_136,A_137,B_138] :
      ( r1_tarski(A_136,A_137)
      | ~ r1_tarski(A_136,k1_relat_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(resolution,[status(thm)],[c_32,c_395])).

tff(c_935,plain,(
    ! [A_30,A_137,B_138] :
      ( r1_tarski(k1_relat_1(A_30),A_137)
      | ~ r1_tarski(A_30,k2_zfmisc_1(A_137,B_138))
      | ~ v1_relat_1(k2_zfmisc_1(A_137,B_138))
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_40,c_931])).

tff(c_7349,plain,(
    ! [A_508,A_509,B_510] :
      ( r1_tarski(k1_relat_1(A_508),A_509)
      | ~ r1_tarski(A_508,k2_zfmisc_1(A_509,B_510))
      | ~ v1_relat_1(A_508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_935])).

tff(c_7453,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_7349])).

tff(c_7538,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_7453])).

tff(c_7540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5019,c_7538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:53:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.05/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.51  
% 7.05/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.51  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.05/2.51  
% 7.05/2.51  %Foreground sorts:
% 7.05/2.51  
% 7.05/2.51  
% 7.05/2.51  %Background operators:
% 7.05/2.51  
% 7.05/2.51  
% 7.05/2.51  %Foreground operators:
% 7.05/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.05/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.05/2.51  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 7.05/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.05/2.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.05/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.05/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.05/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.05/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.05/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.05/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.05/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.05/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.05/2.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.05/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.05/2.51  
% 7.05/2.52  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 7.05/2.52  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.05/2.52  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.05/2.52  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.05/2.52  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 7.05/2.52  tff(f_76, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 7.05/2.52  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.05/2.52  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 7.05/2.52  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 7.05/2.52  tff(f_74, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 7.05/2.52  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.05/2.52  tff(c_131, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.05/2.52  tff(c_140, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_131])).
% 7.05/2.52  tff(c_84, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.52  tff(c_95, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_84])).
% 7.05/2.52  tff(c_30, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.05/2.52  tff(c_1204, plain, (![A_158, B_159]: (r1_tarski(k2_relat_1(A_158), k2_relat_1(B_159)) | ~r1_tarski(A_158, B_159) | ~v1_relat_1(B_159) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.52  tff(c_34, plain, (![A_27, B_28]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_27, B_28)), B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.05/2.52  tff(c_395, plain, (![A_84, C_85, B_86]: (r1_tarski(A_84, C_85) | ~r1_tarski(B_86, C_85) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.05/2.52  tff(c_411, plain, (![A_84, B_28, A_27]: (r1_tarski(A_84, B_28) | ~r1_tarski(A_84, k2_relat_1(k2_zfmisc_1(A_27, B_28))))), inference(resolution, [status(thm)], [c_34, c_395])).
% 7.05/2.52  tff(c_1208, plain, (![A_158, B_28, A_27]: (r1_tarski(k2_relat_1(A_158), B_28) | ~r1_tarski(A_158, k2_zfmisc_1(A_27, B_28)) | ~v1_relat_1(k2_zfmisc_1(A_27, B_28)) | ~v1_relat_1(A_158))), inference(resolution, [status(thm)], [c_1204, c_411])).
% 7.05/2.52  tff(c_4013, plain, (![A_389, B_390, A_391]: (r1_tarski(k2_relat_1(A_389), B_390) | ~r1_tarski(A_389, k2_zfmisc_1(A_391, B_390)) | ~v1_relat_1(A_389))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1208])).
% 7.05/2.52  tff(c_4099, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_95, c_4013])).
% 7.05/2.52  tff(c_4172, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_4099])).
% 7.05/2.52  tff(c_26, plain, (![A_20]: (k2_xboole_0(k1_relat_1(A_20), k2_relat_1(A_20))=k3_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.05/2.52  tff(c_1405, plain, (![A_181, C_182, B_183, D_184]: (r1_tarski(k2_xboole_0(A_181, C_182), k2_xboole_0(B_183, D_184)) | ~r1_tarski(C_182, D_184) | ~r1_tarski(A_181, B_183))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.05/2.52  tff(c_4982, plain, (![A_411, B_412, D_413]: (r1_tarski(k3_relat_1(A_411), k2_xboole_0(B_412, D_413)) | ~r1_tarski(k2_relat_1(A_411), D_413) | ~r1_tarski(k1_relat_1(A_411), B_412) | ~v1_relat_1(A_411))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1405])).
% 7.05/2.52  tff(c_48, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.05/2.52  tff(c_4994, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4982, c_48])).
% 7.05/2.52  tff(c_5019, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_4172, c_4994])).
% 7.05/2.52  tff(c_40, plain, (![A_30, B_32]: (r1_tarski(k1_relat_1(A_30), k1_relat_1(B_32)) | ~r1_tarski(A_30, B_32) | ~v1_relat_1(B_32) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.52  tff(c_32, plain, (![A_25, B_26]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_25, B_26)), A_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.05/2.52  tff(c_931, plain, (![A_136, A_137, B_138]: (r1_tarski(A_136, A_137) | ~r1_tarski(A_136, k1_relat_1(k2_zfmisc_1(A_137, B_138))))), inference(resolution, [status(thm)], [c_32, c_395])).
% 7.05/2.52  tff(c_935, plain, (![A_30, A_137, B_138]: (r1_tarski(k1_relat_1(A_30), A_137) | ~r1_tarski(A_30, k2_zfmisc_1(A_137, B_138)) | ~v1_relat_1(k2_zfmisc_1(A_137, B_138)) | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_40, c_931])).
% 7.05/2.52  tff(c_7349, plain, (![A_508, A_509, B_510]: (r1_tarski(k1_relat_1(A_508), A_509) | ~r1_tarski(A_508, k2_zfmisc_1(A_509, B_510)) | ~v1_relat_1(A_508))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_935])).
% 7.05/2.52  tff(c_7453, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_95, c_7349])).
% 7.05/2.52  tff(c_7538, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_7453])).
% 7.05/2.52  tff(c_7540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5019, c_7538])).
% 7.05/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.52  
% 7.05/2.52  Inference rules
% 7.05/2.52  ----------------------
% 7.05/2.52  #Ref     : 0
% 7.05/2.52  #Sup     : 1591
% 7.05/2.52  #Fact    : 0
% 7.05/2.52  #Define  : 0
% 7.05/2.52  #Split   : 6
% 7.05/2.52  #Chain   : 0
% 7.05/2.52  #Close   : 0
% 7.05/2.52  
% 7.05/2.52  Ordering : KBO
% 7.05/2.52  
% 7.05/2.52  Simplification rules
% 7.05/2.52  ----------------------
% 7.05/2.52  #Subsume      : 191
% 7.05/2.52  #Demod        : 1336
% 7.05/2.52  #Tautology    : 535
% 7.05/2.52  #SimpNegUnit  : 3
% 7.05/2.52  #BackRed      : 9
% 7.05/2.52  
% 7.05/2.52  #Partial instantiations: 0
% 7.05/2.52  #Strategies tried      : 1
% 7.05/2.52  
% 7.05/2.52  Timing (in seconds)
% 7.05/2.52  ----------------------
% 7.05/2.53  Preprocessing        : 0.34
% 7.05/2.53  Parsing              : 0.19
% 7.05/2.53  CNF conversion       : 0.02
% 7.05/2.53  Main loop            : 1.38
% 7.05/2.53  Inferencing          : 0.40
% 7.05/2.53  Reduction            : 0.56
% 7.05/2.53  Demodulation         : 0.45
% 7.05/2.53  BG Simplification    : 0.04
% 7.05/2.53  Subsumption          : 0.28
% 7.05/2.53  Abstraction          : 0.05
% 7.05/2.53  MUC search           : 0.00
% 7.05/2.53  Cooper               : 0.00
% 7.05/2.53  Total                : 1.74
% 7.05/2.53  Index Insertion      : 0.00
% 7.05/2.53  Index Deletion       : 0.00
% 7.05/2.53  Index Matching       : 0.00
% 7.05/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
