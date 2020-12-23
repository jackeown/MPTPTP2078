%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:03 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 203 expanded)
%              Number of leaves         :   33 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 471 expanded)
%              Number of equality atoms :   17 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_101,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

tff(c_34,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    ~ v4_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_79,plain,(
    ! [B_62,A_63] :
      ( l1_pre_topc(B_62)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_85,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_82])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_67,plain,(
    ! [A_18] :
      ( u1_struct_0(A_18) = k2_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_89,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_85,c_67])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_45,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_90,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_45])).

tff(c_68,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_72,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_73,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_42])).

tff(c_38,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [C_73,A_74,B_75] :
      ( r2_hidden(C_73,A_74)
      | ~ r2_hidden(C_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_182,plain,(
    ! [A_89,B_90,A_91] :
      ( r2_hidden('#skF_1'(A_89,B_90),A_91)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(A_91))
      | r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_194,plain,(
    ! [A_92,A_93] :
      ( ~ m1_subset_1(A_92,k1_zfmisc_1(A_93))
      | r1_tarski(A_92,A_93) ) ),
    inference(resolution,[status(thm)],[c_182,c_4])).

tff(c_204,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_194])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_211,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_204,c_8])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_47,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_124,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(A_76,B_77,C_78) = k3_xboole_0(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_133,plain,(
    ! [A_9,B_77] : k9_subset_1(A_9,B_77,A_9) = k3_xboole_0(B_77,A_9) ),
    inference(resolution,[status(thm)],[c_47,c_124])).

tff(c_461,plain,(
    ! [B_127,D_128,A_129] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_127),D_128,k2_struct_0(B_127)),B_127)
      | ~ v4_pre_topc(D_128,A_129)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_127),D_128,k2_struct_0(B_127)),k1_zfmisc_1(u1_struct_0(B_127)))
      | ~ m1_pre_topc(B_127,A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_467,plain,(
    ! [B_127,D_128] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_127),D_128,k2_struct_0(B_127)),B_127)
      | ~ v4_pre_topc(D_128,'#skF_3')
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_127),D_128,k2_struct_0(B_127)),k1_zfmisc_1(u1_struct_0(B_127)))
      | ~ m1_pre_topc(B_127,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_461])).

tff(c_1011,plain,(
    ! [B_231,D_232] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_231),D_232,k2_struct_0(B_231)),B_231)
      | ~ v4_pre_topc(D_232,'#skF_3')
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_231),D_232,k2_struct_0(B_231)),k1_zfmisc_1(u1_struct_0(B_231)))
      | ~ m1_pre_topc(B_231,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_467])).

tff(c_1017,plain,(
    ! [D_232] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_5'),D_232,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v4_pre_topc(D_232,'#skF_3')
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'),D_232,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_1011])).

tff(c_1332,plain,(
    ! [D_273] :
      ( v4_pre_topc(k3_xboole_0(D_273,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v4_pre_topc(D_273,'#skF_3')
      | ~ m1_subset_1(D_273,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_xboole_0(D_273,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_133,c_89,c_133,c_89,c_1017])).

tff(c_1338,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_4',k2_struct_0('#skF_5')),'#skF_5')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_1332])).

tff(c_1344,plain,(
    v4_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_73,c_38,c_211,c_1338])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:08:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.69  
% 3.89/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.70  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.24/1.70  
% 4.24/1.70  %Foreground sorts:
% 4.24/1.70  
% 4.24/1.70  
% 4.24/1.70  %Background operators:
% 4.24/1.70  
% 4.24/1.70  
% 4.24/1.70  %Foreground operators:
% 4.24/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.24/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.24/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.24/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.24/1.70  tff('#skF_6', type, '#skF_6': $i).
% 4.24/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.24/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.24/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.24/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.24/1.70  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.24/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.24/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/1.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.24/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.24/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.24/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.24/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.24/1.70  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.24/1.70  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.24/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.24/1.70  
% 4.24/1.71  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 4.24/1.71  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.24/1.71  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.24/1.71  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.24/1.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.24/1.71  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.24/1.71  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.24/1.71  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.24/1.71  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.24/1.71  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.24/1.71  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v4_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_pre_topc)).
% 4.24/1.71  tff(c_34, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.24/1.71  tff(c_32, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.24/1.71  tff(c_46, plain, (~v4_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 4.24/1.71  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.24/1.71  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.24/1.71  tff(c_79, plain, (![B_62, A_63]: (l1_pre_topc(B_62) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.24/1.71  tff(c_82, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_79])).
% 4.24/1.71  tff(c_85, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_82])).
% 4.24/1.71  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.24/1.71  tff(c_63, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.24/1.71  tff(c_67, plain, (![A_18]: (u1_struct_0(A_18)=k2_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_20, c_63])).
% 4.24/1.71  tff(c_89, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_85, c_67])).
% 4.24/1.71  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.24/1.71  tff(c_45, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 4.24/1.71  tff(c_90, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_45])).
% 4.24/1.71  tff(c_68, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_20, c_63])).
% 4.24/1.71  tff(c_72, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_68])).
% 4.24/1.71  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.24/1.71  tff(c_73, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_42])).
% 4.24/1.71  tff(c_38, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.24/1.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.24/1.71  tff(c_120, plain, (![C_73, A_74, B_75]: (r2_hidden(C_73, A_74) | ~r2_hidden(C_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.24/1.71  tff(c_182, plain, (![A_89, B_90, A_91]: (r2_hidden('#skF_1'(A_89, B_90), A_91) | ~m1_subset_1(A_89, k1_zfmisc_1(A_91)) | r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_6, c_120])).
% 4.24/1.71  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.24/1.71  tff(c_194, plain, (![A_92, A_93]: (~m1_subset_1(A_92, k1_zfmisc_1(A_93)) | r1_tarski(A_92, A_93))), inference(resolution, [status(thm)], [c_182, c_4])).
% 4.24/1.71  tff(c_204, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_90, c_194])).
% 4.24/1.71  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.71  tff(c_211, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_204, c_8])).
% 4.24/1.71  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.24/1.71  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.24/1.71  tff(c_47, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 4.24/1.71  tff(c_124, plain, (![A_76, B_77, C_78]: (k9_subset_1(A_76, B_77, C_78)=k3_xboole_0(B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.24/1.71  tff(c_133, plain, (![A_9, B_77]: (k9_subset_1(A_9, B_77, A_9)=k3_xboole_0(B_77, A_9))), inference(resolution, [status(thm)], [c_47, c_124])).
% 4.24/1.71  tff(c_461, plain, (![B_127, D_128, A_129]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_127), D_128, k2_struct_0(B_127)), B_127) | ~v4_pre_topc(D_128, A_129) | ~m1_subset_1(D_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_127), D_128, k2_struct_0(B_127)), k1_zfmisc_1(u1_struct_0(B_127))) | ~m1_pre_topc(B_127, A_129) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.71  tff(c_467, plain, (![B_127, D_128]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_127), D_128, k2_struct_0(B_127)), B_127) | ~v4_pre_topc(D_128, '#skF_3') | ~m1_subset_1(D_128, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_127), D_128, k2_struct_0(B_127)), k1_zfmisc_1(u1_struct_0(B_127))) | ~m1_pre_topc(B_127, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_461])).
% 4.24/1.71  tff(c_1011, plain, (![B_231, D_232]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_231), D_232, k2_struct_0(B_231)), B_231) | ~v4_pre_topc(D_232, '#skF_3') | ~m1_subset_1(D_232, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_231), D_232, k2_struct_0(B_231)), k1_zfmisc_1(u1_struct_0(B_231))) | ~m1_pre_topc(B_231, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_467])).
% 4.24/1.71  tff(c_1017, plain, (![D_232]: (v4_pre_topc(k9_subset_1(u1_struct_0('#skF_5'), D_232, k2_struct_0('#skF_5')), '#skF_5') | ~v4_pre_topc(D_232, '#skF_3') | ~m1_subset_1(D_232, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'), D_232, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_1011])).
% 4.24/1.71  tff(c_1332, plain, (![D_273]: (v4_pre_topc(k3_xboole_0(D_273, k2_struct_0('#skF_5')), '#skF_5') | ~v4_pre_topc(D_273, '#skF_3') | ~m1_subset_1(D_273, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k3_xboole_0(D_273, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_133, c_89, c_133, c_89, c_1017])).
% 4.24/1.71  tff(c_1338, plain, (v4_pre_topc(k3_xboole_0('#skF_4', k2_struct_0('#skF_5')), '#skF_5') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_211, c_1332])).
% 4.24/1.71  tff(c_1344, plain, (v4_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_73, c_38, c_211, c_1338])).
% 4.24/1.71  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1344])).
% 4.24/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.71  
% 4.24/1.71  Inference rules
% 4.24/1.71  ----------------------
% 4.24/1.71  #Ref     : 0
% 4.24/1.71  #Sup     : 345
% 4.24/1.71  #Fact    : 0
% 4.24/1.71  #Define  : 0
% 4.24/1.71  #Split   : 8
% 4.24/1.71  #Chain   : 0
% 4.24/1.71  #Close   : 0
% 4.24/1.71  
% 4.24/1.71  Ordering : KBO
% 4.24/1.71  
% 4.24/1.71  Simplification rules
% 4.24/1.71  ----------------------
% 4.24/1.71  #Subsume      : 158
% 4.24/1.71  #Demod        : 73
% 4.24/1.71  #Tautology    : 46
% 4.24/1.71  #SimpNegUnit  : 1
% 4.24/1.71  #BackRed      : 2
% 4.24/1.71  
% 4.24/1.71  #Partial instantiations: 0
% 4.24/1.71  #Strategies tried      : 1
% 4.24/1.71  
% 4.24/1.71  Timing (in seconds)
% 4.24/1.71  ----------------------
% 4.24/1.71  Preprocessing        : 0.32
% 4.24/1.71  Parsing              : 0.17
% 4.24/1.71  CNF conversion       : 0.02
% 4.24/1.71  Main loop            : 0.62
% 4.24/1.71  Inferencing          : 0.19
% 4.24/1.71  Reduction            : 0.19
% 4.24/1.71  Demodulation         : 0.13
% 4.24/1.71  BG Simplification    : 0.02
% 4.24/1.71  Subsumption          : 0.19
% 4.24/1.72  Abstraction          : 0.02
% 4.24/1.72  MUC search           : 0.00
% 4.24/1.72  Cooper               : 0.00
% 4.24/1.72  Total                : 0.98
% 4.24/1.72  Index Insertion      : 0.00
% 4.24/1.72  Index Deletion       : 0.00
% 4.24/1.72  Index Matching       : 0.00
% 4.24/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
