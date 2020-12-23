%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:03 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 195 expanded)
%              Number of leaves         :   30 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 458 expanded)
%              Number of equality atoms :   17 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v4_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v4_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v4_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_68,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_69,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_38])).

tff(c_92,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_69,c_92])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    ~ v4_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_74,plain,(
    ! [B_53,A_54] :
      ( l1_pre_topc(B_53)
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_80,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_77])).

tff(c_63,plain,(
    ! [A_11] :
      ( u1_struct_0(A_11) = k2_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_85,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_63])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_41,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_41])).

tff(c_106,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_92])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_131,plain,(
    ! [A_63,B_64,C_65] :
      ( k9_subset_1(A_63,B_64,C_65) = k3_xboole_0(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_143,plain,(
    ! [A_4,B_64] : k9_subset_1(A_4,B_64,A_4) = k3_xboole_0(B_64,A_4) ),
    inference(resolution,[status(thm)],[c_43,c_131])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_403,plain,(
    ! [B_114,D_115,A_116] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_114),D_115,k2_struct_0(B_114)),B_114)
      | ~ v4_pre_topc(D_115,A_116)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_114),D_115,k2_struct_0(B_114)),k1_zfmisc_1(u1_struct_0(B_114)))
      | ~ m1_pre_topc(B_114,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_976,plain,(
    ! [B_159,A_160,A_161] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_159),A_160,k2_struct_0(B_159)),B_159)
      | ~ v4_pre_topc(A_160,A_161)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_159),A_160,k2_struct_0(B_159)),k1_zfmisc_1(u1_struct_0(B_159)))
      | ~ m1_pre_topc(B_159,A_161)
      | ~ l1_pre_topc(A_161)
      | ~ r1_tarski(A_160,u1_struct_0(A_161)) ) ),
    inference(resolution,[status(thm)],[c_12,c_403])).

tff(c_985,plain,(
    ! [A_160,A_161] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),A_160,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_160,A_161)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'),A_160,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_161)
      | ~ l1_pre_topc(A_161)
      | ~ r1_tarski(A_160,u1_struct_0(A_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_976])).

tff(c_1286,plain,(
    ! [A_199,A_200] :
      ( v4_pre_topc(k3_xboole_0(A_199,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_199,A_200)
      | ~ m1_subset_1(k3_xboole_0(A_199,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_200)
      | ~ l1_pre_topc(A_200)
      | ~ r1_tarski(A_199,u1_struct_0(A_200)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_85,c_143,c_85,c_985])).

tff(c_1294,plain,(
    ! [A_200] :
      ( v4_pre_topc(k3_xboole_0('#skF_3',k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc('#skF_3',A_200)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_200)
      | ~ l1_pre_topc(A_200)
      | ~ r1_tarski('#skF_3',u1_struct_0(A_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_1286])).

tff(c_1302,plain,(
    ! [A_200] :
      ( v4_pre_topc('#skF_3','#skF_4')
      | ~ v4_pre_topc('#skF_3',A_200)
      | ~ m1_pre_topc('#skF_4',A_200)
      | ~ l1_pre_topc(A_200)
      | ~ r1_tarski('#skF_3',u1_struct_0(A_200)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_126,c_1294])).

tff(c_1308,plain,(
    ! [A_201] :
      ( ~ v4_pre_topc('#skF_3',A_201)
      | ~ m1_pre_topc('#skF_4',A_201)
      | ~ l1_pre_topc(A_201)
      | ~ r1_tarski('#skF_3',u1_struct_0(A_201)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1302])).

tff(c_1314,plain,
    ( ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1308])).

tff(c_1319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_40,c_36,c_34,c_1314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.65  
% 3.74/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.66  %$ v4_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.74/1.66  
% 3.74/1.66  %Foreground sorts:
% 3.74/1.66  
% 3.74/1.66  
% 3.74/1.66  %Background operators:
% 3.74/1.66  
% 3.74/1.66  
% 3.74/1.66  %Foreground operators:
% 3.74/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.74/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.74/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.74/1.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.74/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.74/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.74/1.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.74/1.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.74/1.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.74/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.66  
% 3.74/1.67  tff(f_91, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 3.74/1.67  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.74/1.67  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.74/1.67  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.74/1.67  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.74/1.67  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.74/1.67  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.74/1.67  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.74/1.67  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.74/1.67  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v4_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_pre_topc)).
% 3.74/1.67  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.74/1.67  tff(c_16, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.74/1.67  tff(c_59, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.74/1.67  tff(c_64, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_16, c_59])).
% 3.74/1.67  tff(c_68, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_64])).
% 3.74/1.67  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.74/1.67  tff(c_69, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_38])).
% 3.74/1.67  tff(c_92, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.67  tff(c_107, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_69, c_92])).
% 3.74/1.67  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.74/1.67  tff(c_34, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.74/1.67  tff(c_30, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.74/1.67  tff(c_28, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.74/1.67  tff(c_42, plain, (~v4_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 3.74/1.67  tff(c_74, plain, (![B_53, A_54]: (l1_pre_topc(B_53) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.74/1.67  tff(c_77, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_74])).
% 3.74/1.67  tff(c_80, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_77])).
% 3.74/1.67  tff(c_63, plain, (![A_11]: (u1_struct_0(A_11)=k2_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_16, c_59])).
% 3.74/1.67  tff(c_85, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_63])).
% 3.74/1.67  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.74/1.67  tff(c_41, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 3.74/1.67  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_41])).
% 3.74/1.67  tff(c_106, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_92])).
% 3.74/1.67  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.74/1.67  tff(c_126, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_106, c_2])).
% 3.74/1.67  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.74/1.67  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.67  tff(c_43, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 3.74/1.67  tff(c_131, plain, (![A_63, B_64, C_65]: (k9_subset_1(A_63, B_64, C_65)=k3_xboole_0(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.67  tff(c_143, plain, (![A_4, B_64]: (k9_subset_1(A_4, B_64, A_4)=k3_xboole_0(B_64, A_4))), inference(resolution, [status(thm)], [c_43, c_131])).
% 3.74/1.67  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.67  tff(c_403, plain, (![B_114, D_115, A_116]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_114), D_115, k2_struct_0(B_114)), B_114) | ~v4_pre_topc(D_115, A_116) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_114), D_115, k2_struct_0(B_114)), k1_zfmisc_1(u1_struct_0(B_114))) | ~m1_pre_topc(B_114, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.74/1.67  tff(c_976, plain, (![B_159, A_160, A_161]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_159), A_160, k2_struct_0(B_159)), B_159) | ~v4_pre_topc(A_160, A_161) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_159), A_160, k2_struct_0(B_159)), k1_zfmisc_1(u1_struct_0(B_159))) | ~m1_pre_topc(B_159, A_161) | ~l1_pre_topc(A_161) | ~r1_tarski(A_160, u1_struct_0(A_161)))), inference(resolution, [status(thm)], [c_12, c_403])).
% 3.74/1.67  tff(c_985, plain, (![A_160, A_161]: (v4_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), A_160, k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc(A_160, A_161) | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'), A_160, k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', A_161) | ~l1_pre_topc(A_161) | ~r1_tarski(A_160, u1_struct_0(A_161)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_976])).
% 3.74/1.67  tff(c_1286, plain, (![A_199, A_200]: (v4_pre_topc(k3_xboole_0(A_199, k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc(A_199, A_200) | ~m1_subset_1(k3_xboole_0(A_199, k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', A_200) | ~l1_pre_topc(A_200) | ~r1_tarski(A_199, u1_struct_0(A_200)))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_85, c_143, c_85, c_985])).
% 3.74/1.67  tff(c_1294, plain, (![A_200]: (v4_pre_topc(k3_xboole_0('#skF_3', k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc('#skF_3', A_200) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', A_200) | ~l1_pre_topc(A_200) | ~r1_tarski('#skF_3', u1_struct_0(A_200)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_1286])).
% 3.74/1.67  tff(c_1302, plain, (![A_200]: (v4_pre_topc('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_3', A_200) | ~m1_pre_topc('#skF_4', A_200) | ~l1_pre_topc(A_200) | ~r1_tarski('#skF_3', u1_struct_0(A_200)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_126, c_1294])).
% 3.74/1.67  tff(c_1308, plain, (![A_201]: (~v4_pre_topc('#skF_3', A_201) | ~m1_pre_topc('#skF_4', A_201) | ~l1_pre_topc(A_201) | ~r1_tarski('#skF_3', u1_struct_0(A_201)))), inference(negUnitSimplification, [status(thm)], [c_42, c_1302])).
% 3.74/1.67  tff(c_1314, plain, (~v4_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1308])).
% 3.74/1.67  tff(c_1319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_40, c_36, c_34, c_1314])).
% 3.74/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.67  
% 3.74/1.67  Inference rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Ref     : 0
% 3.74/1.67  #Sup     : 284
% 3.74/1.67  #Fact    : 0
% 3.74/1.67  #Define  : 0
% 3.74/1.67  #Split   : 5
% 3.74/1.67  #Chain   : 0
% 3.74/1.67  #Close   : 0
% 3.74/1.67  
% 3.74/1.67  Ordering : KBO
% 3.74/1.67  
% 3.74/1.67  Simplification rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Subsume      : 76
% 3.74/1.67  #Demod        : 262
% 3.74/1.67  #Tautology    : 97
% 3.74/1.67  #SimpNegUnit  : 4
% 3.74/1.67  #BackRed      : 2
% 3.74/1.67  
% 3.74/1.67  #Partial instantiations: 0
% 3.74/1.67  #Strategies tried      : 1
% 3.74/1.67  
% 3.74/1.67  Timing (in seconds)
% 3.74/1.67  ----------------------
% 3.74/1.67  Preprocessing        : 0.33
% 3.74/1.67  Parsing              : 0.17
% 3.74/1.67  CNF conversion       : 0.03
% 3.74/1.67  Main loop            : 0.54
% 3.74/1.67  Inferencing          : 0.20
% 3.74/1.67  Reduction            : 0.18
% 3.74/1.67  Demodulation         : 0.13
% 3.74/1.67  BG Simplification    : 0.02
% 3.74/1.67  Subsumption          : 0.10
% 3.74/1.67  Abstraction          : 0.03
% 3.74/1.67  MUC search           : 0.00
% 3.74/1.67  Cooper               : 0.00
% 3.74/1.67  Total                : 0.91
% 3.74/1.67  Index Insertion      : 0.00
% 3.74/1.67  Index Deletion       : 0.00
% 3.74/1.67  Index Matching       : 0.00
% 3.74/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
