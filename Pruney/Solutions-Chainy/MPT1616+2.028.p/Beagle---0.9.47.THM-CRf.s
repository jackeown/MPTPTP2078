%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:39 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 131 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 322 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_60,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    ! [A_13] :
      ( r2_hidden(u1_struct_0(A_13),u1_pre_topc(A_13))
      | ~ v2_pre_topc(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_77,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,k3_tarski(B_37))
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( m1_setfam_1(B_8,A_7)
      | ~ r1_tarski(A_7,k3_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [B_39,A_40] :
      ( m1_setfam_1(B_39,A_40)
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(resolution,[status(thm)],[c_77,c_10])).

tff(c_94,plain,(
    ! [A_13] :
      ( m1_setfam_1(u1_pre_topc(A_13),u1_struct_0(A_13))
      | ~ v2_pre_topc(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_52,c_87])).

tff(c_54,plain,(
    ! [A_27] :
      ( m1_subset_1(u1_pre_topc(A_27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27))))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_120,plain,(
    ! [A_51,B_52] :
      ( k5_setfam_1(A_51,B_52) = A_51
      | ~ m1_setfam_1(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [A_54] :
      ( k5_setfam_1(u1_struct_0(A_54),u1_pre_topc(A_54)) = u1_struct_0(A_54)
      | ~ m1_setfam_1(u1_pre_topc(A_54),u1_struct_0(A_54))
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_54,c_120])).

tff(c_135,plain,(
    ! [A_55] :
      ( k5_setfam_1(u1_struct_0(A_55),u1_pre_topc(A_55)) = u1_struct_0(A_55)
      | ~ v2_pre_topc(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_94,c_126])).

tff(c_100,plain,(
    ! [A_45,B_46] :
      ( k5_setfam_1(A_45,B_46) = k3_tarski(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_27] :
      ( k5_setfam_1(u1_struct_0(A_27),u1_pre_topc(A_27)) = k3_tarski(u1_pre_topc(A_27))
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_141,plain,(
    ! [A_55] :
      ( k3_tarski(u1_pre_topc(A_55)) = u1_struct_0(A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_104])).

tff(c_150,plain,(
    ! [A_56] :
      ( k3_tarski(u1_pre_topc(A_56)) = u1_struct_0(A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_104])).

tff(c_56,plain,(
    ! [A_28] :
      ( k4_yellow_0(k2_yellow_1(A_28)) = k3_tarski(A_28)
      | ~ r2_hidden(k3_tarski(A_28),A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_291,plain,(
    ! [A_78] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_78))) = k3_tarski(u1_pre_topc(A_78))
      | ~ r2_hidden(u1_struct_0(A_78),u1_pre_topc(A_78))
      | v1_xboole_0(u1_pre_topc(A_78))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_56])).

tff(c_296,plain,(
    ! [A_79] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_79))) = k3_tarski(u1_pre_topc(A_79))
      | v1_xboole_0(u1_pre_topc(A_79))
      | ~ v2_pre_topc(A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_52,c_291])).

tff(c_58,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5'))) != u1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_302,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_58])).

tff(c_308,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_302])).

tff(c_310,plain,(
    k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_313,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_310])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_313])).

tff(c_318,plain,(
    v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_82,plain,(
    ! [A_38] :
      ( r2_hidden(u1_struct_0(A_38),u1_pre_topc(A_38))
      | ~ v2_pre_topc(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_pre_topc(A_38))
      | ~ v2_pre_topc(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_328,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_318,c_86])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.39  
% 2.59/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.39  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_3
% 2.59/1.39  
% 2.59/1.39  %Foreground sorts:
% 2.59/1.39  
% 2.59/1.39  
% 2.59/1.39  %Background operators:
% 2.59/1.39  
% 2.59/1.39  
% 2.59/1.39  %Foreground operators:
% 2.59/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.59/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.59/1.39  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.59/1.39  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.59/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.39  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.59/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.39  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.59/1.39  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.59/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.59/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.59/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.39  
% 2.59/1.40  tff(f_95, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 2.59/1.40  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.59/1.40  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.59/1.40  tff(f_39, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.59/1.40  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.59/1.40  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.59/1.40  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.59/1.40  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.59/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.59/1.40  tff(c_60, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.59/1.40  tff(c_62, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.59/1.40  tff(c_52, plain, (![A_13]: (r2_hidden(u1_struct_0(A_13), u1_pre_topc(A_13)) | ~v2_pre_topc(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.40  tff(c_77, plain, (![A_36, B_37]: (r1_tarski(A_36, k3_tarski(B_37)) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.40  tff(c_10, plain, (![B_8, A_7]: (m1_setfam_1(B_8, A_7) | ~r1_tarski(A_7, k3_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.40  tff(c_87, plain, (![B_39, A_40]: (m1_setfam_1(B_39, A_40) | ~r2_hidden(A_40, B_39))), inference(resolution, [status(thm)], [c_77, c_10])).
% 2.59/1.40  tff(c_94, plain, (![A_13]: (m1_setfam_1(u1_pre_topc(A_13), u1_struct_0(A_13)) | ~v2_pre_topc(A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_52, c_87])).
% 2.59/1.40  tff(c_54, plain, (![A_27]: (m1_subset_1(u1_pre_topc(A_27), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27)))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.40  tff(c_120, plain, (![A_51, B_52]: (k5_setfam_1(A_51, B_52)=A_51 | ~m1_setfam_1(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.40  tff(c_126, plain, (![A_54]: (k5_setfam_1(u1_struct_0(A_54), u1_pre_topc(A_54))=u1_struct_0(A_54) | ~m1_setfam_1(u1_pre_topc(A_54), u1_struct_0(A_54)) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_54, c_120])).
% 2.59/1.40  tff(c_135, plain, (![A_55]: (k5_setfam_1(u1_struct_0(A_55), u1_pre_topc(A_55))=u1_struct_0(A_55) | ~v2_pre_topc(A_55) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_94, c_126])).
% 2.59/1.40  tff(c_100, plain, (![A_45, B_46]: (k5_setfam_1(A_45, B_46)=k3_tarski(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.40  tff(c_104, plain, (![A_27]: (k5_setfam_1(u1_struct_0(A_27), u1_pre_topc(A_27))=k3_tarski(u1_pre_topc(A_27)) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_54, c_100])).
% 2.59/1.40  tff(c_141, plain, (![A_55]: (k3_tarski(u1_pre_topc(A_55))=u1_struct_0(A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | ~l1_pre_topc(A_55))), inference(superposition, [status(thm), theory('equality')], [c_135, c_104])).
% 2.59/1.40  tff(c_150, plain, (![A_56]: (k3_tarski(u1_pre_topc(A_56))=u1_struct_0(A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | ~l1_pre_topc(A_56))), inference(superposition, [status(thm), theory('equality')], [c_135, c_104])).
% 2.59/1.40  tff(c_56, plain, (![A_28]: (k4_yellow_0(k2_yellow_1(A_28))=k3_tarski(A_28) | ~r2_hidden(k3_tarski(A_28), A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.40  tff(c_291, plain, (![A_78]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_78)))=k3_tarski(u1_pre_topc(A_78)) | ~r2_hidden(u1_struct_0(A_78), u1_pre_topc(A_78)) | v1_xboole_0(u1_pre_topc(A_78)) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | ~l1_pre_topc(A_78))), inference(superposition, [status(thm), theory('equality')], [c_150, c_56])).
% 2.59/1.40  tff(c_296, plain, (![A_79]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_79)))=k3_tarski(u1_pre_topc(A_79)) | v1_xboole_0(u1_pre_topc(A_79)) | ~v2_pre_topc(A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_52, c_291])).
% 2.59/1.40  tff(c_58, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5')))!=u1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.59/1.40  tff(c_302, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5')) | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_296, c_58])).
% 2.59/1.40  tff(c_308, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_302])).
% 2.59/1.40  tff(c_310, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_308])).
% 2.59/1.40  tff(c_313, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_141, c_310])).
% 2.59/1.40  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_313])).
% 2.59/1.40  tff(c_318, plain, (v1_xboole_0(u1_pre_topc('#skF_5'))), inference(splitRight, [status(thm)], [c_308])).
% 2.59/1.40  tff(c_82, plain, (![A_38]: (r2_hidden(u1_struct_0(A_38), u1_pre_topc(A_38)) | ~v2_pre_topc(A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.40  tff(c_86, plain, (![A_38]: (~v1_xboole_0(u1_pre_topc(A_38)) | ~v2_pre_topc(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_82, c_2])).
% 2.59/1.40  tff(c_328, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_318, c_86])).
% 2.59/1.40  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_328])).
% 2.59/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.40  
% 2.59/1.40  Inference rules
% 2.59/1.40  ----------------------
% 2.59/1.40  #Ref     : 0
% 2.59/1.40  #Sup     : 58
% 2.59/1.40  #Fact    : 0
% 2.59/1.40  #Define  : 0
% 2.59/1.40  #Split   : 1
% 2.59/1.41  #Chain   : 0
% 2.59/1.41  #Close   : 0
% 2.59/1.41  
% 2.59/1.41  Ordering : KBO
% 2.59/1.41  
% 2.59/1.41  Simplification rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Subsume      : 8
% 2.59/1.41  #Demod        : 6
% 2.59/1.41  #Tautology    : 18
% 2.59/1.41  #SimpNegUnit  : 0
% 2.59/1.41  #BackRed      : 0
% 2.59/1.41  
% 2.59/1.41  #Partial instantiations: 0
% 2.59/1.41  #Strategies tried      : 1
% 2.59/1.41  
% 2.59/1.41  Timing (in seconds)
% 2.59/1.41  ----------------------
% 2.59/1.41  Preprocessing        : 0.34
% 2.59/1.41  Parsing              : 0.18
% 2.59/1.41  CNF conversion       : 0.02
% 2.59/1.41  Main loop            : 0.26
% 2.59/1.41  Inferencing          : 0.10
% 2.59/1.41  Reduction            : 0.06
% 2.59/1.41  Demodulation         : 0.04
% 2.59/1.41  BG Simplification    : 0.02
% 2.59/1.41  Subsumption          : 0.05
% 2.59/1.41  Abstraction          : 0.01
% 2.59/1.41  MUC search           : 0.00
% 2.59/1.41  Cooper               : 0.00
% 2.59/1.41  Total                : 0.63
% 2.59/1.41  Index Insertion      : 0.00
% 2.59/1.41  Index Deletion       : 0.00
% 2.59/1.41  Index Matching       : 0.00
% 2.59/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
