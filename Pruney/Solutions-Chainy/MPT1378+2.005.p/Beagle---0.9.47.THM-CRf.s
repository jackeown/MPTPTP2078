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
% DateTime   : Thu Dec  3 10:24:04 EST 2020

% Result     : Theorem 9.48s
% Output     : CNFRefutation 9.48s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 111 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  136 ( 374 expanded)
%              Number of equality atoms :    5 (  13 expanded)
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

tff(f_120,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_83,axiom,(
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

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_148,plain,(
    ! [A_94,B_95,C_96] :
      ( k4_subset_1(A_94,B_95,C_96) = k2_xboole_0(B_95,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_249,plain,(
    ! [B_101] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_101,'#skF_5') = k2_xboole_0(B_101,'#skF_5')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_148])).

tff(c_277,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_249])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k4_subset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_283,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_16])).

tff(c_287,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_283])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(k2_xboole_0(A_47,B_49),C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_47,B_49] : r1_tarski(A_47,k2_xboole_0(A_47,B_49)) ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_20,plain,(
    ! [A_17,B_21,C_23] :
      ( r1_tarski(k1_tops_1(A_17,B_21),k1_tops_1(A_17,C_23))
      | ~ r1_tarski(B_21,C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_447,plain,(
    ! [B_105,A_106,C_107] :
      ( r2_hidden(B_105,k1_tops_1(A_106,C_107))
      | ~ m1_connsp_2(C_107,A_106,B_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_105,u1_struct_0(A_106))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_476,plain,(
    ! [B_105] :
      ( r2_hidden(B_105,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_105)
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_447])).

tff(c_530,plain,(
    ! [B_105] :
      ( r2_hidden(B_105,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_105)
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_476])).

tff(c_536,plain,(
    ! [B_108] :
      ( r2_hidden(B_108,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_108)
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_530])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_906,plain,(
    ! [B_163,B_164] :
      ( r2_hidden(B_163,B_164)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_164)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_163)
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_536,c_2])).

tff(c_918,plain,(
    ! [B_163,C_23] :
      ( r2_hidden(B_163,k1_tops_1('#skF_2',C_23))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_163)
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_4',C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_906])).

tff(c_8109,plain,(
    ! [B_302,C_303] :
      ( r2_hidden(B_302,k1_tops_1('#skF_2',C_303))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_302)
      | ~ m1_subset_1(B_302,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_4',C_303)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_918])).

tff(c_8231,plain,(
    ! [B_302] :
      ( r2_hidden(B_302,k1_tops_1('#skF_2',k2_xboole_0('#skF_4','#skF_5')))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_302)
      | ~ m1_subset_1(B_302,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_287,c_8109])).

tff(c_8379,plain,(
    ! [B_304] :
      ( r2_hidden(B_304,k1_tops_1('#skF_2',k2_xboole_0('#skF_4','#skF_5')))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_304)
      | ~ m1_subset_1(B_304,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8231])).

tff(c_22,plain,(
    ! [C_30,A_24,B_28] :
      ( m1_connsp_2(C_30,A_24,B_28)
      | ~ r2_hidden(B_28,k1_tops_1(A_24,C_30))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8381,plain,(
    ! [B_304] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_304)
      | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_304)
      | ~ m1_subset_1(B_304,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8379,c_22])).

tff(c_8390,plain,(
    ! [B_304] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_304)
      | v2_struct_0('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_304)
      | ~ m1_subset_1(B_304,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_287,c_8381])).

tff(c_8394,plain,(
    ! [B_305] :
      ( m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2',B_305)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_305)
      | ~ m1_subset_1(B_305,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_8390])).

tff(c_28,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_279,plain,(
    ~ m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_28])).

tff(c_8397,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8394,c_279])).

tff(c_8403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_8397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:23:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.48/3.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.48/3.36  
% 9.48/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.48/3.37  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.48/3.37  
% 9.48/3.37  %Foreground sorts:
% 9.48/3.37  
% 9.48/3.37  
% 9.48/3.37  %Background operators:
% 9.48/3.37  
% 9.48/3.37  
% 9.48/3.37  %Foreground operators:
% 9.48/3.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.48/3.37  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 9.48/3.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.48/3.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.48/3.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.48/3.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.48/3.37  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.48/3.37  tff('#skF_5', type, '#skF_5': $i).
% 9.48/3.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.48/3.37  tff('#skF_2', type, '#skF_2': $i).
% 9.48/3.37  tff('#skF_3', type, '#skF_3': $i).
% 9.48/3.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.48/3.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.48/3.37  tff('#skF_4', type, '#skF_4': $i).
% 9.48/3.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.48/3.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.48/3.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.48/3.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.48/3.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.48/3.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.48/3.37  
% 9.48/3.38  tff(f_120, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) => m1_connsp_2(k4_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_connsp_2)).
% 9.48/3.38  tff(f_54, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.48/3.38  tff(f_48, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 9.48/3.38  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.48/3.38  tff(f_42, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.48/3.38  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 9.48/3.38  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 9.48/3.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.48/3.38  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.48/3.38  tff(c_32, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.48/3.38  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.48/3.38  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.48/3.38  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.48/3.38  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.48/3.38  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.48/3.38  tff(c_148, plain, (![A_94, B_95, C_96]: (k4_subset_1(A_94, B_95, C_96)=k2_xboole_0(B_95, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.48/3.38  tff(c_249, plain, (![B_101]: (k4_subset_1(u1_struct_0('#skF_2'), B_101, '#skF_5')=k2_xboole_0(B_101, '#skF_5') | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_148])).
% 9.48/3.38  tff(c_277, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_249])).
% 9.48/3.38  tff(c_16, plain, (![A_11, B_12, C_13]: (m1_subset_1(k4_subset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.48/3.38  tff(c_283, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_277, c_16])).
% 9.48/3.38  tff(c_287, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_283])).
% 9.48/3.38  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.48/3.38  tff(c_47, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(k2_xboole_0(A_47, B_49), C_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.48/3.38  tff(c_52, plain, (![A_47, B_49]: (r1_tarski(A_47, k2_xboole_0(A_47, B_49)))), inference(resolution, [status(thm)], [c_12, c_47])).
% 9.48/3.38  tff(c_20, plain, (![A_17, B_21, C_23]: (r1_tarski(k1_tops_1(A_17, B_21), k1_tops_1(A_17, C_23)) | ~r1_tarski(B_21, C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.48/3.38  tff(c_447, plain, (![B_105, A_106, C_107]: (r2_hidden(B_105, k1_tops_1(A_106, C_107)) | ~m1_connsp_2(C_107, A_106, B_105) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_105, u1_struct_0(A_106)) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.48/3.38  tff(c_476, plain, (![B_105]: (r2_hidden(B_105, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_105) | ~m1_subset_1(B_105, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_447])).
% 9.48/3.38  tff(c_530, plain, (![B_105]: (r2_hidden(B_105, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_105) | ~m1_subset_1(B_105, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_476])).
% 9.48/3.38  tff(c_536, plain, (![B_108]: (r2_hidden(B_108, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_108) | ~m1_subset_1(B_108, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_530])).
% 9.48/3.38  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.48/3.38  tff(c_906, plain, (![B_163, B_164]: (r2_hidden(B_163, B_164) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_164) | ~m1_connsp_2('#skF_4', '#skF_2', B_163) | ~m1_subset_1(B_163, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_536, c_2])).
% 9.48/3.38  tff(c_918, plain, (![B_163, C_23]: (r2_hidden(B_163, k1_tops_1('#skF_2', C_23)) | ~m1_connsp_2('#skF_4', '#skF_2', B_163) | ~m1_subset_1(B_163, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_906])).
% 9.48/3.38  tff(c_8109, plain, (![B_302, C_303]: (r2_hidden(B_302, k1_tops_1('#skF_2', C_303)) | ~m1_connsp_2('#skF_4', '#skF_2', B_302) | ~m1_subset_1(B_302, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', C_303) | ~m1_subset_1(C_303, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_918])).
% 9.48/3.38  tff(c_8231, plain, (![B_302]: (r2_hidden(B_302, k1_tops_1('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))) | ~m1_connsp_2('#skF_4', '#skF_2', B_302) | ~m1_subset_1(B_302, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_287, c_8109])).
% 9.48/3.38  tff(c_8379, plain, (![B_304]: (r2_hidden(B_304, k1_tops_1('#skF_2', k2_xboole_0('#skF_4', '#skF_5'))) | ~m1_connsp_2('#skF_4', '#skF_2', B_304) | ~m1_subset_1(B_304, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8231])).
% 9.48/3.38  tff(c_22, plain, (![C_30, A_24, B_28]: (m1_connsp_2(C_30, A_24, B_28) | ~r2_hidden(B_28, k1_tops_1(A_24, C_30)) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_28, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.48/3.38  tff(c_8381, plain, (![B_304]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_304) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_304) | ~m1_subset_1(B_304, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8379, c_22])).
% 9.48/3.38  tff(c_8390, plain, (![B_304]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_304) | v2_struct_0('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_304) | ~m1_subset_1(B_304, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_287, c_8381])).
% 9.48/3.38  tff(c_8394, plain, (![B_305]: (m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', B_305) | ~m1_connsp_2('#skF_4', '#skF_2', B_305) | ~m1_subset_1(B_305, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_8390])).
% 9.48/3.38  tff(c_28, plain, (~m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.48/3.38  tff(c_279, plain, (~m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_28])).
% 9.48/3.38  tff(c_8397, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8394, c_279])).
% 9.48/3.38  tff(c_8403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_8397])).
% 9.48/3.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.48/3.38  
% 9.48/3.38  Inference rules
% 9.48/3.38  ----------------------
% 9.48/3.38  #Ref     : 0
% 9.48/3.38  #Sup     : 1834
% 9.48/3.38  #Fact    : 0
% 9.48/3.38  #Define  : 0
% 9.48/3.38  #Split   : 1
% 9.48/3.38  #Chain   : 0
% 9.48/3.38  #Close   : 0
% 9.48/3.38  
% 9.48/3.38  Ordering : KBO
% 9.48/3.38  
% 9.48/3.38  Simplification rules
% 9.48/3.38  ----------------------
% 9.48/3.38  #Subsume      : 26
% 9.48/3.38  #Demod        : 3411
% 9.48/3.38  #Tautology    : 216
% 9.48/3.38  #SimpNegUnit  : 432
% 9.48/3.38  #BackRed      : 1
% 9.48/3.38  
% 9.48/3.38  #Partial instantiations: 0
% 9.48/3.38  #Strategies tried      : 1
% 9.48/3.38  
% 9.48/3.38  Timing (in seconds)
% 9.48/3.38  ----------------------
% 9.48/3.38  Preprocessing        : 0.31
% 9.48/3.38  Parsing              : 0.16
% 9.48/3.38  CNF conversion       : 0.02
% 9.48/3.38  Main loop            : 2.26
% 9.48/3.38  Inferencing          : 0.53
% 9.48/3.38  Reduction            : 1.01
% 9.48/3.38  Demodulation         : 0.83
% 9.48/3.38  BG Simplification    : 0.07
% 9.48/3.38  Subsumption          : 0.51
% 9.48/3.38  Abstraction          : 0.11
% 9.48/3.38  MUC search           : 0.00
% 9.48/3.38  Cooper               : 0.00
% 9.48/3.38  Total                : 2.60
% 9.48/3.38  Index Insertion      : 0.00
% 9.48/3.39  Index Deletion       : 0.00
% 9.48/3.39  Index Matching       : 0.00
% 9.48/3.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
