%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:05 EST 2020

% Result     : Theorem 8.62s
% Output     : CNFRefutation 8.62s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 108 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 367 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( m1_connsp_2(C,A,B)
                        & m1_connsp_2(D,A,B) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(A),C,D),A,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_59,plain,(
    ! [A_52,B_53,C_54] :
      ( k4_subset_1(A_52,B_53,C_54) = k2_xboole_0(B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,(
    ! [B_56] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_56,'#skF_5') = k2_xboole_0(B_56,'#skF_5')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_90,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_117,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1(k4_subset_1(A_65,B_66,C_67),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_133,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_117])).

tff(c_146,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_133])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_tarski(k1_tops_1(A_14,B_18),k1_tops_1(A_14,C_20))
      | ~ r1_tarski(B_18,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_438,plain,(
    ! [B_96,A_97,C_98] :
      ( r2_hidden(B_96,k1_tops_1(A_97,C_98))
      | ~ m1_connsp_2(C_98,A_97,B_96)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_96,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_469,plain,(
    ! [B_96] :
      ( r2_hidden(B_96,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_96)
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_438])).

tff(c_527,plain,(
    ! [B_96] :
      ( r2_hidden(B_96,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_96)
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_469])).

tff(c_533,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_527])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_717,plain,(
    ! [B_132,B_133] :
      ( r2_hidden(B_132,B_133)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_133)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_132)
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_729,plain,(
    ! [B_132,C_20] :
      ( r2_hidden(B_132,k1_tops_1('#skF_2',C_20))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_132)
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_4',C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_717])).

tff(c_7121,plain,(
    ! [B_207,C_208] :
      ( r2_hidden(B_207,k1_tops_1('#skF_2',C_208))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_207)
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_4',C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_729])).

tff(c_7249,plain,(
    ! [B_207] :
      ( r2_hidden(B_207,k1_tops_1('#skF_2',k2_xboole_0('#skF_4','#skF_5')))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_207)
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_146,c_7121])).

tff(c_7411,plain,(
    ! [B_211] :
      ( r2_hidden(B_211,k1_tops_1('#skF_2',k2_xboole_0('#skF_4','#skF_5')))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_211)
      | ~ m1_subset_1(B_211,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7249])).

tff(c_16,plain,(
    ! [C_27,A_21,B_25] :
      ( m1_connsp_2(C_27,A_21,B_25)
      | ~ r2_hidden(B_25,k1_tops_1(A_21,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_25,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_7413,plain,(
    ! [B_211] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_211)
      | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_211)
      | ~ m1_subset_1(B_211,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_7411,c_16])).

tff(c_7422,plain,(
    ! [B_211] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_211)
      | v2_struct_0('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_211)
      | ~ m1_subset_1(B_211,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_146,c_7413])).

tff(c_7426,plain,(
    ! [B_212] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_212)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_212)
      | ~ m1_subset_1(B_212,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_7422])).

tff(c_20,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_92,plain,(
    ~ m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_20])).

tff(c_7429,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7426,c_92])).

tff(c_7433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_7429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.62/2.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.62/2.99  
% 8.62/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.62/2.99  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.62/2.99  
% 8.62/2.99  %Foreground sorts:
% 8.62/2.99  
% 8.62/2.99  
% 8.62/2.99  %Background operators:
% 8.62/2.99  
% 8.62/2.99  
% 8.62/2.99  %Foreground operators:
% 8.62/2.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.62/2.99  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 8.62/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.62/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.62/2.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.62/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.62/2.99  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.62/2.99  tff('#skF_5', type, '#skF_5': $i).
% 8.62/2.99  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.62/2.99  tff('#skF_2', type, '#skF_2': $i).
% 8.62/2.99  tff('#skF_3', type, '#skF_3': $i).
% 8.62/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.62/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.62/2.99  tff('#skF_4', type, '#skF_4': $i).
% 8.62/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.62/2.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.62/2.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.62/2.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.62/2.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.62/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.62/2.99  
% 8.62/3.00  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) => m1_connsp_2(k4_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_connsp_2)).
% 8.62/3.00  tff(f_46, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.62/3.00  tff(f_40, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 8.62/3.00  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.62/3.00  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 8.62/3.00  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 8.62/3.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.62/3.00  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.00  tff(c_24, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.00  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.00  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.00  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.00  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.00  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.00  tff(c_59, plain, (![A_52, B_53, C_54]: (k4_subset_1(A_52, B_53, C_54)=k2_xboole_0(B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.62/3.00  tff(c_83, plain, (![B_56]: (k4_subset_1(u1_struct_0('#skF_2'), B_56, '#skF_5')=k2_xboole_0(B_56, '#skF_5') | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_26, c_59])).
% 8.62/3.00  tff(c_90, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_83])).
% 8.62/3.00  tff(c_117, plain, (![A_65, B_66, C_67]: (m1_subset_1(k4_subset_1(A_65, B_66, C_67), k1_zfmisc_1(A_65)) | ~m1_subset_1(C_67, k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.62/3.00  tff(c_133, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_117])).
% 8.62/3.00  tff(c_146, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_133])).
% 8.62/3.00  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.62/3.00  tff(c_14, plain, (![A_14, B_18, C_20]: (r1_tarski(k1_tops_1(A_14, B_18), k1_tops_1(A_14, C_20)) | ~r1_tarski(B_18, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.62/3.00  tff(c_438, plain, (![B_96, A_97, C_98]: (r2_hidden(B_96, k1_tops_1(A_97, C_98)) | ~m1_connsp_2(C_98, A_97, B_96) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(B_96, u1_struct_0(A_97)) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.62/3.00  tff(c_469, plain, (![B_96]: (r2_hidden(B_96, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_96) | ~m1_subset_1(B_96, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_438])).
% 8.62/3.00  tff(c_527, plain, (![B_96]: (r2_hidden(B_96, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_96) | ~m1_subset_1(B_96, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_469])).
% 8.62/3.00  tff(c_533, plain, (![B_99]: (r2_hidden(B_99, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_527])).
% 8.62/3.00  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.62/3.00  tff(c_717, plain, (![B_132, B_133]: (r2_hidden(B_132, B_133) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_133) | ~m1_connsp_2('#skF_4', '#skF_2', B_132) | ~m1_subset_1(B_132, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_533, c_2])).
% 8.62/3.00  tff(c_729, plain, (![B_132, C_20]: (r2_hidden(B_132, k1_tops_1('#skF_2', C_20)) | ~m1_connsp_2('#skF_4', '#skF_2', B_132) | ~m1_subset_1(B_132, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_717])).
% 8.62/3.00  tff(c_7121, plain, (![B_207, C_208]: (r2_hidden(B_207, k1_tops_1('#skF_2', C_208)) | ~m1_connsp_2('#skF_4', '#skF_2', B_207) | ~m1_subset_1(B_207, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_729])).
% 8.62/3.00  tff(c_7249, plain, (![B_207]: (r2_hidden(B_207, k1_tops_1('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))) | ~m1_connsp_2('#skF_4', '#skF_2', B_207) | ~m1_subset_1(B_207, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_146, c_7121])).
% 8.62/3.00  tff(c_7411, plain, (![B_211]: (r2_hidden(B_211, k1_tops_1('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))) | ~m1_connsp_2('#skF_4', '#skF_2', B_211) | ~m1_subset_1(B_211, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7249])).
% 8.62/3.00  tff(c_16, plain, (![C_27, A_21, B_25]: (m1_connsp_2(C_27, A_21, B_25) | ~r2_hidden(B_25, k1_tops_1(A_21, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_25, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.62/3.00  tff(c_7413, plain, (![B_211]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_211) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_211) | ~m1_subset_1(B_211, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_7411, c_16])).
% 8.62/3.00  tff(c_7422, plain, (![B_211]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_211) | v2_struct_0('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_211) | ~m1_subset_1(B_211, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_146, c_7413])).
% 8.62/3.00  tff(c_7426, plain, (![B_212]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_212) | ~m1_connsp_2('#skF_4', '#skF_2', B_212) | ~m1_subset_1(B_212, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_7422])).
% 8.62/3.00  tff(c_20, plain, (~m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.00  tff(c_92, plain, (~m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_20])).
% 8.62/3.00  tff(c_7429, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_7426, c_92])).
% 8.62/3.00  tff(c_7433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_7429])).
% 8.62/3.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.62/3.00  
% 8.62/3.00  Inference rules
% 8.62/3.00  ----------------------
% 8.62/3.00  #Ref     : 0
% 8.62/3.00  #Sup     : 1616
% 8.62/3.00  #Fact    : 0
% 8.62/3.00  #Define  : 0
% 8.62/3.00  #Split   : 0
% 8.62/3.00  #Chain   : 0
% 8.62/3.00  #Close   : 0
% 8.62/3.00  
% 8.62/3.00  Ordering : KBO
% 8.62/3.00  
% 8.62/3.00  Simplification rules
% 8.62/3.00  ----------------------
% 8.62/3.00  #Subsume      : 20
% 8.62/3.00  #Demod        : 3321
% 8.62/3.00  #Tautology    : 179
% 8.62/3.00  #SimpNegUnit  : 423
% 8.62/3.00  #BackRed      : 1
% 8.62/3.00  
% 8.62/3.00  #Partial instantiations: 0
% 8.62/3.00  #Strategies tried      : 1
% 8.62/3.00  
% 8.62/3.00  Timing (in seconds)
% 8.62/3.00  ----------------------
% 8.62/3.01  Preprocessing        : 0.30
% 8.62/3.01  Parsing              : 0.15
% 8.62/3.01  CNF conversion       : 0.02
% 8.62/3.01  Main loop            : 1.90
% 8.62/3.01  Inferencing          : 0.46
% 8.62/3.01  Reduction            : 0.87
% 8.62/3.01  Demodulation         : 0.72
% 8.62/3.01  BG Simplification    : 0.06
% 8.62/3.01  Subsumption          : 0.40
% 8.62/3.01  Abstraction          : 0.10
% 8.62/3.01  MUC search           : 0.00
% 8.62/3.01  Cooper               : 0.00
% 8.62/3.01  Total                : 2.22
% 8.62/3.01  Index Insertion      : 0.00
% 8.62/3.01  Index Deletion       : 0.00
% 8.62/3.01  Index Matching       : 0.00
% 8.62/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
