%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:01 EST 2020

% Result     : Theorem 9.49s
% Output     : CNFRefutation 9.49s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 205 expanded)
%              Number of leaves         :   35 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 471 expanded)
%              Number of equality atoms :   17 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v3_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v3_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_38,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    ~ v3_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_82,plain,(
    ! [B_69,A_70] :
      ( l1_pre_topc(B_69)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_88,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_85])).

tff(c_22,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [A_67] :
      ( u1_struct_0(A_67) = k2_struct_0(A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71,plain,(
    ! [A_20] :
      ( u1_struct_0(A_20) = k2_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_93,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_71])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_94,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_49])).

tff(c_72,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_76,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_72])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_77,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46])).

tff(c_42,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,(
    ! [C_84,A_85,B_86] :
      ( r2_hidden(C_84,A_85)
      | ~ r2_hidden(C_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,(
    ! [A_97,B_98,A_99] :
      ( r2_hidden('#skF_1'(A_97,B_98),A_99)
      | ~ m1_subset_1(A_97,k1_zfmisc_1(A_99))
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_6,c_133])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_198,plain,(
    ! [A_100,A_101] :
      ( ~ m1_subset_1(A_100,k1_zfmisc_1(A_101))
      | r1_tarski(A_100,A_101) ) ),
    inference(resolution,[status(thm)],[c_186,c_4])).

tff(c_208,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_94,c_198])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_215,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_208,c_8])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_137,plain,(
    ! [A_87,B_88,C_89] :
      ( k9_subset_1(A_87,B_88,C_89) = k3_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,(
    ! [A_9,B_88] : k9_subset_1(A_9,B_88,A_9) = k3_xboole_0(B_88,A_9) ),
    inference(resolution,[status(thm)],[c_51,c_137])).

tff(c_726,plain,(
    ! [B_148,D_149,A_150] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_148),D_149,k2_struct_0(B_148)),B_148)
      | ~ v3_pre_topc(D_149,A_150)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_148),D_149,k2_struct_0(B_148)),k1_zfmisc_1(u1_struct_0(B_148)))
      | ~ m1_pre_topc(B_148,A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_740,plain,(
    ! [B_148,D_149] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_148),D_149,k2_struct_0(B_148)),B_148)
      | ~ v3_pre_topc(D_149,'#skF_3')
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_148),D_149,k2_struct_0(B_148)),k1_zfmisc_1(u1_struct_0(B_148)))
      | ~ m1_pre_topc(B_148,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_726])).

tff(c_12103,plain,(
    ! [B_939,D_940] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_939),D_940,k2_struct_0(B_939)),B_939)
      | ~ v3_pre_topc(D_940,'#skF_3')
      | ~ m1_subset_1(D_940,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_939),D_940,k2_struct_0(B_939)),k1_zfmisc_1(u1_struct_0(B_939)))
      | ~ m1_pre_topc(B_939,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_740])).

tff(c_12129,plain,(
    ! [D_940] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_5'),D_940,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v3_pre_topc(D_940,'#skF_3')
      | ~ m1_subset_1(D_940,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'),D_940,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12103])).

tff(c_12804,plain,(
    ! [D_977] :
      ( v3_pre_topc(k3_xboole_0(D_977,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v3_pre_topc(D_977,'#skF_3')
      | ~ m1_subset_1(D_977,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_xboole_0(D_977,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_146,c_93,c_146,c_93,c_12129])).

tff(c_12813,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_4',k2_struct_0('#skF_5')),'#skF_5')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_12804])).

tff(c_12819,plain,(
    v3_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_77,c_42,c_215,c_12813])).

tff(c_12821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_12819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.49/3.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.85  
% 9.49/3.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.85  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 9.49/3.85  
% 9.49/3.85  %Foreground sorts:
% 9.49/3.85  
% 9.49/3.85  
% 9.49/3.85  %Background operators:
% 9.49/3.85  
% 9.49/3.85  
% 9.49/3.85  %Foreground operators:
% 9.49/3.85  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.49/3.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.49/3.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.49/3.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.49/3.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.49/3.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.49/3.85  tff('#skF_5', type, '#skF_5': $i).
% 9.49/3.85  tff('#skF_6', type, '#skF_6': $i).
% 9.49/3.85  tff('#skF_3', type, '#skF_3': $i).
% 9.49/3.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.49/3.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.49/3.85  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.49/3.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.49/3.85  tff('#skF_4', type, '#skF_4': $i).
% 9.49/3.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.49/3.85  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.49/3.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.49/3.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.49/3.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.49/3.85  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.49/3.85  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.49/3.85  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.49/3.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.49/3.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.49/3.85  
% 9.49/3.86  tff(f_113, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 9.49/3.86  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.49/3.86  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.49/3.86  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.49/3.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.49/3.86  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.49/3.86  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.49/3.86  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.49/3.86  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.49/3.86  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.49/3.86  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 9.49/3.86  tff(c_38, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.49/3.86  tff(c_36, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.49/3.86  tff(c_50, plain, (~v3_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 9.49/3.86  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.49/3.86  tff(c_44, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.49/3.86  tff(c_82, plain, (![B_69, A_70]: (l1_pre_topc(B_69) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.49/3.86  tff(c_85, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_82])).
% 9.49/3.86  tff(c_88, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_85])).
% 9.49/3.86  tff(c_22, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.49/3.86  tff(c_67, plain, (![A_67]: (u1_struct_0(A_67)=k2_struct_0(A_67) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.49/3.86  tff(c_71, plain, (![A_20]: (u1_struct_0(A_20)=k2_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_22, c_67])).
% 9.49/3.86  tff(c_93, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_88, c_71])).
% 9.49/3.86  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.49/3.86  tff(c_49, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 9.49/3.86  tff(c_94, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_49])).
% 9.49/3.86  tff(c_72, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_22, c_67])).
% 9.49/3.86  tff(c_76, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_72])).
% 9.49/3.86  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.49/3.86  tff(c_77, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46])).
% 9.49/3.86  tff(c_42, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.49/3.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.49/3.86  tff(c_133, plain, (![C_84, A_85, B_86]: (r2_hidden(C_84, A_85) | ~r2_hidden(C_84, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.49/3.86  tff(c_186, plain, (![A_97, B_98, A_99]: (r2_hidden('#skF_1'(A_97, B_98), A_99) | ~m1_subset_1(A_97, k1_zfmisc_1(A_99)) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_6, c_133])).
% 9.49/3.86  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.49/3.86  tff(c_198, plain, (![A_100, A_101]: (~m1_subset_1(A_100, k1_zfmisc_1(A_101)) | r1_tarski(A_100, A_101))), inference(resolution, [status(thm)], [c_186, c_4])).
% 9.49/3.86  tff(c_208, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_94, c_198])).
% 9.49/3.86  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.49/3.86  tff(c_215, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_208, c_8])).
% 9.49/3.86  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.49/3.86  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.49/3.86  tff(c_51, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 9.49/3.86  tff(c_137, plain, (![A_87, B_88, C_89]: (k9_subset_1(A_87, B_88, C_89)=k3_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.49/3.86  tff(c_146, plain, (![A_9, B_88]: (k9_subset_1(A_9, B_88, A_9)=k3_xboole_0(B_88, A_9))), inference(resolution, [status(thm)], [c_51, c_137])).
% 9.49/3.86  tff(c_726, plain, (![B_148, D_149, A_150]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_148), D_149, k2_struct_0(B_148)), B_148) | ~v3_pre_topc(D_149, A_150) | ~m1_subset_1(D_149, k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_148), D_149, k2_struct_0(B_148)), k1_zfmisc_1(u1_struct_0(B_148))) | ~m1_pre_topc(B_148, A_150) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.49/3.86  tff(c_740, plain, (![B_148, D_149]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_148), D_149, k2_struct_0(B_148)), B_148) | ~v3_pre_topc(D_149, '#skF_3') | ~m1_subset_1(D_149, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_148), D_149, k2_struct_0(B_148)), k1_zfmisc_1(u1_struct_0(B_148))) | ~m1_pre_topc(B_148, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_726])).
% 9.49/3.86  tff(c_12103, plain, (![B_939, D_940]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_939), D_940, k2_struct_0(B_939)), B_939) | ~v3_pre_topc(D_940, '#skF_3') | ~m1_subset_1(D_940, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_939), D_940, k2_struct_0(B_939)), k1_zfmisc_1(u1_struct_0(B_939))) | ~m1_pre_topc(B_939, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_740])).
% 9.49/3.86  tff(c_12129, plain, (![D_940]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_5'), D_940, k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc(D_940, '#skF_3') | ~m1_subset_1(D_940, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'), D_940, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_12103])).
% 9.49/3.86  tff(c_12804, plain, (![D_977]: (v3_pre_topc(k3_xboole_0(D_977, k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc(D_977, '#skF_3') | ~m1_subset_1(D_977, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k3_xboole_0(D_977, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_146, c_93, c_146, c_93, c_12129])).
% 9.49/3.86  tff(c_12813, plain, (v3_pre_topc(k3_xboole_0('#skF_4', k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_215, c_12804])).
% 9.49/3.86  tff(c_12819, plain, (v3_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_77, c_42, c_215, c_12813])).
% 9.49/3.86  tff(c_12821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_12819])).
% 9.49/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.86  
% 9.49/3.86  Inference rules
% 9.49/3.86  ----------------------
% 9.49/3.86  #Ref     : 0
% 9.49/3.86  #Sup     : 3479
% 9.49/3.86  #Fact    : 0
% 9.49/3.86  #Define  : 0
% 9.49/3.86  #Split   : 23
% 9.49/3.86  #Chain   : 0
% 9.49/3.86  #Close   : 0
% 9.49/3.86  
% 9.49/3.86  Ordering : KBO
% 9.49/3.86  
% 9.49/3.86  Simplification rules
% 9.49/3.86  ----------------------
% 9.49/3.86  #Subsume      : 2316
% 9.49/3.86  #Demod        : 834
% 9.49/3.86  #Tautology    : 293
% 9.49/3.86  #SimpNegUnit  : 1
% 9.49/3.86  #BackRed      : 2
% 9.49/3.86  
% 9.49/3.86  #Partial instantiations: 0
% 9.49/3.86  #Strategies tried      : 1
% 9.49/3.86  
% 9.49/3.86  Timing (in seconds)
% 9.49/3.86  ----------------------
% 9.49/3.87  Preprocessing        : 0.33
% 9.49/3.87  Parsing              : 0.18
% 9.49/3.87  CNF conversion       : 0.03
% 9.49/3.87  Main loop            : 2.76
% 9.49/3.87  Inferencing          : 0.70
% 9.49/3.87  Reduction            : 0.72
% 9.49/3.87  Demodulation         : 0.48
% 9.49/3.87  BG Simplification    : 0.05
% 9.49/3.87  Subsumption          : 1.17
% 9.49/3.87  Abstraction          : 0.09
% 9.49/3.87  MUC search           : 0.00
% 9.49/3.87  Cooper               : 0.00
% 9.49/3.87  Total                : 3.12
% 9.49/3.87  Index Insertion      : 0.00
% 9.49/3.87  Index Deletion       : 0.00
% 9.49/3.87  Index Matching       : 0.00
% 9.49/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
