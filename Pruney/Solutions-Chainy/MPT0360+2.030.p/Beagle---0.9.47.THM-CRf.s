%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:22 EST 2020

% Result     : Theorem 15.74s
% Output     : CNFRefutation 15.74s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 161 expanded)
%              Number of leaves         :   30 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 355 expanded)
%              Number of equality atoms :   27 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_56,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ! [C_19,A_15] :
      ( r2_hidden(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_145,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5111,plain,(
    ! [C_331,A_332] :
      ( m1_subset_1(C_331,k1_zfmisc_1(A_332))
      | v1_xboole_0(k1_zfmisc_1(A_332))
      | ~ r1_tarski(C_331,A_332) ) ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_48,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k3_subset_1(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32062,plain,(
    ! [A_936,C_937] :
      ( k4_xboole_0(A_936,C_937) = k3_subset_1(A_936,C_937)
      | v1_xboole_0(k1_zfmisc_1(A_936))
      | ~ r1_tarski(C_937,A_936) ) ),
    inference(resolution,[status(thm)],[c_5111,c_48])).

tff(c_32140,plain,
    ( k4_xboole_0('#skF_9','#skF_8') = k3_subset_1('#skF_9','#skF_8')
    | v1_xboole_0(k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_56,c_32062])).

tff(c_32141,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_32140])).

tff(c_72,plain,(
    ! [C_35,A_36] :
      ( r2_hidden(C_35,k1_zfmisc_1(A_36))
      | ~ r1_tarski(C_35,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_36,C_35] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_36))
      | ~ r1_tarski(C_35,A_36) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_32188,plain,(
    ! [C_35] : ~ r1_tarski(C_35,'#skF_9') ),
    inference(resolution,[status(thm)],[c_32141,c_76])).

tff(c_32192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32188,c_56])).

tff(c_32194,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_32140])).

tff(c_159,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32139,plain,
    ( k4_xboole_0(k3_subset_1('#skF_7','#skF_9'),'#skF_8') = k3_subset_1(k3_subset_1('#skF_7','#skF_9'),'#skF_8')
    | v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_7','#skF_9'))) ),
    inference(resolution,[status(thm)],[c_54,c_32062])).

tff(c_33261,plain,(
    v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_32139])).

tff(c_33308,plain,(
    ! [C_35] : ~ r1_tarski(C_35,k3_subset_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_33261,c_76])).

tff(c_33311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33308,c_54])).

tff(c_33313,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_32139])).

tff(c_24,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_4'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [D_43,A_44,B_45] :
      ( r2_hidden(D_43,A_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3906,plain,(
    ! [A_260,B_261] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_260,B_261)),A_260)
      | k4_xboole_0(A_260,B_261) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_103])).

tff(c_114,plain,(
    ! [D_46,B_47,A_48] :
      ( ~ r2_hidden(D_46,B_47)
      | ~ r2_hidden(D_46,k4_xboole_0(A_48,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [A_48,B_47] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_48,B_47)),B_47)
      | k4_xboole_0(A_48,B_47) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_3942,plain,(
    ! [A_260] : k4_xboole_0(A_260,A_260) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3906,c_124])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4469,plain,(
    ! [A_287,B_288,C_289] :
      ( ~ r2_hidden('#skF_2'(A_287,B_288,C_289),B_288)
      | r2_hidden('#skF_3'(A_287,B_288,C_289),C_289)
      | k4_xboole_0(A_287,B_288) = C_289 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4472,plain,(
    ! [A_5,C_7] :
      ( r2_hidden('#skF_3'(A_5,A_5,C_7),C_7)
      | k4_xboole_0(A_5,A_5) = C_7 ) ),
    inference(resolution,[status(thm)],[c_22,c_4469])).

tff(c_4651,plain,(
    ! [A_298,C_299] :
      ( r2_hidden('#skF_3'(A_298,A_298,C_299),C_299)
      | k1_xboole_0 = C_299 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3942,c_4472])).

tff(c_50,plain,(
    ! [C_27,A_24,B_25] :
      ( r2_hidden(C_27,A_24)
      | ~ r2_hidden(C_27,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4692,plain,(
    ! [A_298,C_299,A_24] :
      ( r2_hidden('#skF_3'(A_298,A_298,C_299),A_24)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(A_24))
      | k1_xboole_0 = C_299 ) ),
    inference(resolution,[status(thm)],[c_4651,c_50])).

tff(c_39150,plain,(
    ! [A_1022,C_1023,A_1024] :
      ( r2_hidden('#skF_3'(A_1022,A_1022,C_1023),A_1024)
      | ~ m1_subset_1(C_1023,k1_zfmisc_1(A_1024))
      | k1_xboole_0 = C_1023 ) ),
    inference(resolution,[status(thm)],[c_4651,c_50])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_183,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_202,plain,(
    k4_xboole_0('#skF_7','#skF_9') = k3_subset_1('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_183])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_219,plain,(
    ! [D_10] :
      ( ~ r2_hidden(D_10,'#skF_9')
      | ~ r2_hidden(D_10,k3_subset_1('#skF_7','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_8])).

tff(c_43560,plain,(
    ! [A_1093,C_1094] :
      ( ~ r2_hidden('#skF_3'(A_1093,A_1093,C_1094),'#skF_9')
      | ~ m1_subset_1(C_1094,k1_zfmisc_1(k3_subset_1('#skF_7','#skF_9')))
      | k1_xboole_0 = C_1094 ) ),
    inference(resolution,[status(thm)],[c_39150,c_219])).

tff(c_43738,plain,(
    ! [C_1100] :
      ( ~ m1_subset_1(C_1100,k1_zfmisc_1(k3_subset_1('#skF_7','#skF_9')))
      | ~ m1_subset_1(C_1100,k1_zfmisc_1('#skF_9'))
      | k1_xboole_0 = C_1100 ) ),
    inference(resolution,[status(thm)],[c_4692,c_43560])).

tff(c_43806,plain,(
    ! [C_19] :
      ( ~ m1_subset_1(C_19,k1_zfmisc_1('#skF_9'))
      | k1_xboole_0 = C_19
      | v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_7','#skF_9')))
      | ~ r1_tarski(C_19,k3_subset_1('#skF_7','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_159,c_43738])).

tff(c_43877,plain,(
    ! [C_1101] :
      ( ~ m1_subset_1(C_1101,k1_zfmisc_1('#skF_9'))
      | k1_xboole_0 = C_1101
      | ~ r1_tarski(C_1101,k3_subset_1('#skF_7','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_33313,c_43806])).

tff(c_43992,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_9'))
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_54,c_43877])).

tff(c_44025,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_43992])).

tff(c_44028,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_9'))
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_159,c_44025])).

tff(c_44034,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44028])).

tff(c_44036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32194,c_44034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.74/8.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.74/8.05  
% 15.74/8.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.74/8.05  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 15.74/8.05  
% 15.74/8.05  %Foreground sorts:
% 15.74/8.05  
% 15.74/8.05  
% 15.74/8.05  %Background operators:
% 15.74/8.05  
% 15.74/8.05  
% 15.74/8.05  %Foreground operators:
% 15.74/8.05  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 15.74/8.05  tff('#skF_4', type, '#skF_4': $i > $i).
% 15.74/8.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.74/8.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.74/8.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.74/8.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.74/8.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.74/8.05  tff('#skF_7', type, '#skF_7': $i).
% 15.74/8.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.74/8.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.74/8.05  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.74/8.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.74/8.05  tff('#skF_9', type, '#skF_9': $i).
% 15.74/8.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.74/8.05  tff('#skF_8', type, '#skF_8': $i).
% 15.74/8.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.74/8.05  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.74/8.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.74/8.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.74/8.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.74/8.05  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 15.74/8.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.74/8.05  
% 15.74/8.06  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 15.74/8.06  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 15.74/8.06  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 15.74/8.06  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 15.74/8.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 15.74/8.06  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 15.74/8.06  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 15.74/8.06  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 15.74/8.06  tff(c_56, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.74/8.06  tff(c_30, plain, (![C_19, A_15]: (r2_hidden(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.74/8.06  tff(c_145, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.74/8.06  tff(c_5111, plain, (![C_331, A_332]: (m1_subset_1(C_331, k1_zfmisc_1(A_332)) | v1_xboole_0(k1_zfmisc_1(A_332)) | ~r1_tarski(C_331, A_332))), inference(resolution, [status(thm)], [c_30, c_145])).
% 15.74/8.06  tff(c_48, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k3_subset_1(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.74/8.06  tff(c_32062, plain, (![A_936, C_937]: (k4_xboole_0(A_936, C_937)=k3_subset_1(A_936, C_937) | v1_xboole_0(k1_zfmisc_1(A_936)) | ~r1_tarski(C_937, A_936))), inference(resolution, [status(thm)], [c_5111, c_48])).
% 15.74/8.06  tff(c_32140, plain, (k4_xboole_0('#skF_9', '#skF_8')=k3_subset_1('#skF_9', '#skF_8') | v1_xboole_0(k1_zfmisc_1('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_32062])).
% 15.74/8.06  tff(c_32141, plain, (v1_xboole_0(k1_zfmisc_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_32140])).
% 15.74/8.06  tff(c_72, plain, (![C_35, A_36]: (r2_hidden(C_35, k1_zfmisc_1(A_36)) | ~r1_tarski(C_35, A_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.74/8.06  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.74/8.06  tff(c_76, plain, (![A_36, C_35]: (~v1_xboole_0(k1_zfmisc_1(A_36)) | ~r1_tarski(C_35, A_36))), inference(resolution, [status(thm)], [c_72, c_2])).
% 15.74/8.06  tff(c_32188, plain, (![C_35]: (~r1_tarski(C_35, '#skF_9'))), inference(resolution, [status(thm)], [c_32141, c_76])).
% 15.74/8.06  tff(c_32192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32188, c_56])).
% 15.74/8.06  tff(c_32194, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_9'))), inference(splitRight, [status(thm)], [c_32140])).
% 15.74/8.06  tff(c_159, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(resolution, [status(thm)], [c_30, c_145])).
% 15.74/8.06  tff(c_52, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.74/8.06  tff(c_54, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.74/8.06  tff(c_32139, plain, (k4_xboole_0(k3_subset_1('#skF_7', '#skF_9'), '#skF_8')=k3_subset_1(k3_subset_1('#skF_7', '#skF_9'), '#skF_8') | v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_7', '#skF_9')))), inference(resolution, [status(thm)], [c_54, c_32062])).
% 15.74/8.06  tff(c_33261, plain, (v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_32139])).
% 15.74/8.06  tff(c_33308, plain, (![C_35]: (~r1_tarski(C_35, k3_subset_1('#skF_7', '#skF_9')))), inference(resolution, [status(thm)], [c_33261, c_76])).
% 15.74/8.06  tff(c_33311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33308, c_54])).
% 15.74/8.06  tff(c_33313, plain, (~v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_32139])).
% 15.74/8.06  tff(c_24, plain, (![A_11]: (r2_hidden('#skF_4'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.74/8.06  tff(c_103, plain, (![D_43, A_44, B_45]: (r2_hidden(D_43, A_44) | ~r2_hidden(D_43, k4_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.74/8.06  tff(c_3906, plain, (![A_260, B_261]: (r2_hidden('#skF_4'(k4_xboole_0(A_260, B_261)), A_260) | k4_xboole_0(A_260, B_261)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_103])).
% 15.74/8.06  tff(c_114, plain, (![D_46, B_47, A_48]: (~r2_hidden(D_46, B_47) | ~r2_hidden(D_46, k4_xboole_0(A_48, B_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.74/8.06  tff(c_124, plain, (![A_48, B_47]: (~r2_hidden('#skF_4'(k4_xboole_0(A_48, B_47)), B_47) | k4_xboole_0(A_48, B_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_114])).
% 15.74/8.06  tff(c_3942, plain, (![A_260]: (k4_xboole_0(A_260, A_260)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3906, c_124])).
% 15.74/8.06  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.74/8.06  tff(c_4469, plain, (![A_287, B_288, C_289]: (~r2_hidden('#skF_2'(A_287, B_288, C_289), B_288) | r2_hidden('#skF_3'(A_287, B_288, C_289), C_289) | k4_xboole_0(A_287, B_288)=C_289)), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.74/8.06  tff(c_4472, plain, (![A_5, C_7]: (r2_hidden('#skF_3'(A_5, A_5, C_7), C_7) | k4_xboole_0(A_5, A_5)=C_7)), inference(resolution, [status(thm)], [c_22, c_4469])).
% 15.74/8.06  tff(c_4651, plain, (![A_298, C_299]: (r2_hidden('#skF_3'(A_298, A_298, C_299), C_299) | k1_xboole_0=C_299)), inference(demodulation, [status(thm), theory('equality')], [c_3942, c_4472])).
% 15.74/8.06  tff(c_50, plain, (![C_27, A_24, B_25]: (r2_hidden(C_27, A_24) | ~r2_hidden(C_27, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.74/8.06  tff(c_4692, plain, (![A_298, C_299, A_24]: (r2_hidden('#skF_3'(A_298, A_298, C_299), A_24) | ~m1_subset_1(C_299, k1_zfmisc_1(A_24)) | k1_xboole_0=C_299)), inference(resolution, [status(thm)], [c_4651, c_50])).
% 15.74/8.06  tff(c_39150, plain, (![A_1022, C_1023, A_1024]: (r2_hidden('#skF_3'(A_1022, A_1022, C_1023), A_1024) | ~m1_subset_1(C_1023, k1_zfmisc_1(A_1024)) | k1_xboole_0=C_1023)), inference(resolution, [status(thm)], [c_4651, c_50])).
% 15.74/8.06  tff(c_58, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.74/8.06  tff(c_183, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.74/8.06  tff(c_202, plain, (k4_xboole_0('#skF_7', '#skF_9')=k3_subset_1('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_58, c_183])).
% 15.74/8.06  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.74/8.06  tff(c_219, plain, (![D_10]: (~r2_hidden(D_10, '#skF_9') | ~r2_hidden(D_10, k3_subset_1('#skF_7', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_202, c_8])).
% 15.74/8.06  tff(c_43560, plain, (![A_1093, C_1094]: (~r2_hidden('#skF_3'(A_1093, A_1093, C_1094), '#skF_9') | ~m1_subset_1(C_1094, k1_zfmisc_1(k3_subset_1('#skF_7', '#skF_9'))) | k1_xboole_0=C_1094)), inference(resolution, [status(thm)], [c_39150, c_219])).
% 15.74/8.06  tff(c_43738, plain, (![C_1100]: (~m1_subset_1(C_1100, k1_zfmisc_1(k3_subset_1('#skF_7', '#skF_9'))) | ~m1_subset_1(C_1100, k1_zfmisc_1('#skF_9')) | k1_xboole_0=C_1100)), inference(resolution, [status(thm)], [c_4692, c_43560])).
% 15.74/8.06  tff(c_43806, plain, (![C_19]: (~m1_subset_1(C_19, k1_zfmisc_1('#skF_9')) | k1_xboole_0=C_19 | v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_7', '#skF_9'))) | ~r1_tarski(C_19, k3_subset_1('#skF_7', '#skF_9')))), inference(resolution, [status(thm)], [c_159, c_43738])).
% 15.74/8.06  tff(c_43877, plain, (![C_1101]: (~m1_subset_1(C_1101, k1_zfmisc_1('#skF_9')) | k1_xboole_0=C_1101 | ~r1_tarski(C_1101, k3_subset_1('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_33313, c_43806])).
% 15.74/8.06  tff(c_43992, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_9')) | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_54, c_43877])).
% 15.74/8.06  tff(c_44025, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_52, c_43992])).
% 15.74/8.06  tff(c_44028, plain, (v1_xboole_0(k1_zfmisc_1('#skF_9')) | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_159, c_44025])).
% 15.74/8.06  tff(c_44034, plain, (v1_xboole_0(k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44028])).
% 15.74/8.06  tff(c_44036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32194, c_44034])).
% 15.74/8.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.74/8.06  
% 15.74/8.06  Inference rules
% 15.74/8.06  ----------------------
% 15.74/8.06  #Ref     : 0
% 15.74/8.06  #Sup     : 10895
% 15.74/8.06  #Fact    : 0
% 15.74/8.06  #Define  : 0
% 15.74/8.06  #Split   : 45
% 15.74/8.06  #Chain   : 0
% 15.74/8.06  #Close   : 0
% 15.74/8.07  
% 15.74/8.07  Ordering : KBO
% 15.74/8.07  
% 15.74/8.07  Simplification rules
% 15.74/8.07  ----------------------
% 15.74/8.07  #Subsume      : 4899
% 15.74/8.07  #Demod        : 3389
% 15.74/8.07  #Tautology    : 1231
% 15.74/8.07  #SimpNegUnit  : 804
% 15.74/8.07  #BackRed      : 144
% 15.74/8.07  
% 15.74/8.07  #Partial instantiations: 0
% 15.74/8.07  #Strategies tried      : 1
% 15.74/8.07  
% 15.74/8.07  Timing (in seconds)
% 15.74/8.07  ----------------------
% 15.74/8.07  Preprocessing        : 0.34
% 15.74/8.07  Parsing              : 0.17
% 15.74/8.07  CNF conversion       : 0.03
% 15.74/8.07  Main loop            : 6.90
% 15.74/8.07  Inferencing          : 1.41
% 15.74/8.07  Reduction            : 2.11
% 15.74/8.07  Demodulation         : 1.43
% 15.74/8.07  BG Simplification    : 0.14
% 15.74/8.07  Subsumption          : 2.74
% 15.74/8.07  Abstraction          : 0.20
% 15.74/8.07  MUC search           : 0.00
% 15.74/8.07  Cooper               : 0.00
% 15.74/8.07  Total                : 7.28
% 15.74/8.07  Index Insertion      : 0.00
% 15.74/8.07  Index Deletion       : 0.00
% 15.74/8.07  Index Matching       : 0.00
% 15.74/8.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
