%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:05 EST 2020

% Result     : Theorem 19.45s
% Output     : CNFRefutation 19.45s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 105 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  161 ( 336 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_118,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_59,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_59,c_4])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_43,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_51,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_43])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(k2_xboole_0(A_9,C_11),B_10)
      | ~ r1_tarski(C_11,B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_18,plain,(
    ! [A_17,B_21,C_23] :
      ( r1_tarski(k1_tops_1(A_17,B_21),k1_tops_1(A_17,C_23))
      | ~ r1_tarski(B_21,C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_773,plain,(
    ! [B_112,A_113,C_114] :
      ( r2_hidden(B_112,k1_tops_1(A_113,C_114))
      | ~ m1_connsp_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(B_112,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1243,plain,(
    ! [B_129,A_130,A_131] :
      ( r2_hidden(B_129,k1_tops_1(A_130,A_131))
      | ~ m1_connsp_2(A_131,A_130,B_129)
      | ~ m1_subset_1(B_129,u1_struct_0(A_130))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130)
      | ~ r1_tarski(A_131,u1_struct_0(A_130)) ) ),
    inference(resolution,[status(thm)],[c_16,c_773])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2907,plain,(
    ! [B_188,B_189,A_190,A_191] :
      ( r2_hidden(B_188,B_189)
      | ~ r1_tarski(k1_tops_1(A_190,A_191),B_189)
      | ~ m1_connsp_2(A_191,A_190,B_188)
      | ~ m1_subset_1(B_188,u1_struct_0(A_190))
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190)
      | ~ r1_tarski(A_191,u1_struct_0(A_190)) ) ),
    inference(resolution,[status(thm)],[c_1243,c_2])).

tff(c_7573,plain,(
    ! [B_474,A_475,C_476,B_477] :
      ( r2_hidden(B_474,k1_tops_1(A_475,C_476))
      | ~ m1_connsp_2(B_477,A_475,B_474)
      | ~ m1_subset_1(B_474,u1_struct_0(A_475))
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475)
      | ~ r1_tarski(B_477,u1_struct_0(A_475))
      | ~ r1_tarski(B_477,C_476)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ l1_pre_topc(A_475) ) ),
    inference(resolution,[status(thm)],[c_18,c_2907])).

tff(c_7583,plain,(
    ! [C_476] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_476))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_5',u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5',C_476)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_7573])).

tff(c_7602,plain,(
    ! [C_476] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_476))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_5',C_476)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_51,c_40,c_36,c_7583])).

tff(c_7604,plain,(
    ! [C_478] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_478))
      | ~ r1_tarski('#skF_5',C_478)
      | ~ m1_subset_1(C_478,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_7602])).

tff(c_7703,plain,(
    ! [A_480] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',A_480))
      | ~ r1_tarski('#skF_5',A_480)
      | ~ r1_tarski(A_480,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_7604])).

tff(c_20,plain,(
    ! [C_30,A_24,B_28] :
      ( m1_connsp_2(C_30,A_24,B_28)
      | ~ r2_hidden(B_28,k1_tops_1(A_24,C_30))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7705,plain,(
    ! [A_480] :
      ( m1_connsp_2(A_480,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_480,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_5',A_480)
      | ~ r1_tarski(A_480,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_7703,c_20])).

tff(c_7710,plain,(
    ! [A_480] :
      ( m1_connsp_2(A_480,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_480,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_5',A_480)
      | ~ r1_tarski(A_480,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_7705])).

tff(c_8263,plain,(
    ! [A_531] :
      ( m1_connsp_2(A_531,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_531,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_5',A_531)
      | ~ r1_tarski(A_531,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_7710])).

tff(c_8295,plain,(
    ! [A_532] :
      ( m1_connsp_2(A_532,'#skF_2','#skF_3')
      | ~ r1_tarski('#skF_5',A_532)
      | ~ r1_tarski(A_532,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_8263])).

tff(c_41363,plain,(
    ! [A_2229,C_2230] :
      ( m1_connsp_2(k2_xboole_0(A_2229,C_2230),'#skF_2','#skF_3')
      | ~ r1_tarski('#skF_5',k2_xboole_0(A_2229,C_2230))
      | ~ r1_tarski(C_2230,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_2229,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_8295])).

tff(c_71,plain,(
    ! [A_64,B_65,C_66] :
      ( k4_subset_1(A_64,B_65,C_66) = k2_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,(
    ! [B_70] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_70,'#skF_5') = k2_xboole_0(B_70,'#skF_5')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_102,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_90])).

tff(c_26,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_104,plain,(
    ~ m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_26])).

tff(c_41376,plain,
    ( ~ r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_41363,c_104])).

tff(c_41399,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_51,c_41376])).

tff(c_41402,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_41399])).

tff(c_41406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_41402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.45/11.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.45/11.22  
% 19.45/11.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.45/11.22  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 19.45/11.22  
% 19.45/11.22  %Foreground sorts:
% 19.45/11.22  
% 19.45/11.22  
% 19.45/11.22  %Background operators:
% 19.45/11.22  
% 19.45/11.22  
% 19.45/11.22  %Foreground operators:
% 19.45/11.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.45/11.22  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 19.45/11.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.45/11.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.45/11.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.45/11.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.45/11.22  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 19.45/11.22  tff('#skF_5', type, '#skF_5': $i).
% 19.45/11.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 19.45/11.22  tff('#skF_2', type, '#skF_2': $i).
% 19.45/11.22  tff('#skF_3', type, '#skF_3': $i).
% 19.45/11.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.45/11.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.45/11.22  tff('#skF_4', type, '#skF_4': $i).
% 19.45/11.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.45/11.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.45/11.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.45/11.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.45/11.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.45/11.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.45/11.22  
% 19.45/11.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 19.45/11.24  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 19.45/11.24  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) => m1_connsp_2(k4_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_connsp_2)).
% 19.45/11.24  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 19.45/11.24  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 19.45/11.24  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 19.45/11.24  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 19.45/11.24  tff(f_48, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 19.45/11.24  tff(c_59, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.45/11.24  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.45/11.24  tff(c_64, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_59, c_4])).
% 19.45/11.24  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 19.45/11.24  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.45/11.24  tff(c_43, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.45/11.24  tff(c_50, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_43])).
% 19.45/11.24  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.45/11.24  tff(c_51, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_43])).
% 19.45/11.24  tff(c_10, plain, (![A_9, C_11, B_10]: (r1_tarski(k2_xboole_0(A_9, C_11), B_10) | ~r1_tarski(C_11, B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.45/11.24  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.45/11.24  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.45/11.24  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.45/11.24  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.45/11.24  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.45/11.24  tff(c_28, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.45/11.24  tff(c_18, plain, (![A_17, B_21, C_23]: (r1_tarski(k1_tops_1(A_17, B_21), k1_tops_1(A_17, C_23)) | ~r1_tarski(B_21, C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.45/11.24  tff(c_773, plain, (![B_112, A_113, C_114]: (r2_hidden(B_112, k1_tops_1(A_113, C_114)) | ~m1_connsp_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(B_112, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.45/11.24  tff(c_1243, plain, (![B_129, A_130, A_131]: (r2_hidden(B_129, k1_tops_1(A_130, A_131)) | ~m1_connsp_2(A_131, A_130, B_129) | ~m1_subset_1(B_129, u1_struct_0(A_130)) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130) | ~r1_tarski(A_131, u1_struct_0(A_130)))), inference(resolution, [status(thm)], [c_16, c_773])).
% 19.45/11.24  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.45/11.24  tff(c_2907, plain, (![B_188, B_189, A_190, A_191]: (r2_hidden(B_188, B_189) | ~r1_tarski(k1_tops_1(A_190, A_191), B_189) | ~m1_connsp_2(A_191, A_190, B_188) | ~m1_subset_1(B_188, u1_struct_0(A_190)) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190) | ~r1_tarski(A_191, u1_struct_0(A_190)))), inference(resolution, [status(thm)], [c_1243, c_2])).
% 19.45/11.24  tff(c_7573, plain, (![B_474, A_475, C_476, B_477]: (r2_hidden(B_474, k1_tops_1(A_475, C_476)) | ~m1_connsp_2(B_477, A_475, B_474) | ~m1_subset_1(B_474, u1_struct_0(A_475)) | ~v2_pre_topc(A_475) | v2_struct_0(A_475) | ~r1_tarski(B_477, u1_struct_0(A_475)) | ~r1_tarski(B_477, C_476) | ~m1_subset_1(C_476, k1_zfmisc_1(u1_struct_0(A_475))) | ~m1_subset_1(B_477, k1_zfmisc_1(u1_struct_0(A_475))) | ~l1_pre_topc(A_475))), inference(resolution, [status(thm)], [c_18, c_2907])).
% 19.45/11.24  tff(c_7583, plain, (![C_476]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_476)) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5', u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', C_476) | ~m1_subset_1(C_476, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_7573])).
% 19.45/11.24  tff(c_7602, plain, (![C_476]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_476)) | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5', C_476) | ~m1_subset_1(C_476, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_51, c_40, c_36, c_7583])).
% 19.45/11.24  tff(c_7604, plain, (![C_478]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_478)) | ~r1_tarski('#skF_5', C_478) | ~m1_subset_1(C_478, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_7602])).
% 19.45/11.24  tff(c_7703, plain, (![A_480]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', A_480)) | ~r1_tarski('#skF_5', A_480) | ~r1_tarski(A_480, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_7604])).
% 19.45/11.24  tff(c_20, plain, (![C_30, A_24, B_28]: (m1_connsp_2(C_30, A_24, B_28) | ~r2_hidden(B_28, k1_tops_1(A_24, C_30)) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_28, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.45/11.24  tff(c_7705, plain, (![A_480]: (m1_connsp_2(A_480, '#skF_2', '#skF_3') | ~m1_subset_1(A_480, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5', A_480) | ~r1_tarski(A_480, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_7703, c_20])).
% 19.45/11.24  tff(c_7710, plain, (![A_480]: (m1_connsp_2(A_480, '#skF_2', '#skF_3') | ~m1_subset_1(A_480, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5', A_480) | ~r1_tarski(A_480, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_7705])).
% 19.45/11.24  tff(c_8263, plain, (![A_531]: (m1_connsp_2(A_531, '#skF_2', '#skF_3') | ~m1_subset_1(A_531, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_5', A_531) | ~r1_tarski(A_531, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_7710])).
% 19.45/11.24  tff(c_8295, plain, (![A_532]: (m1_connsp_2(A_532, '#skF_2', '#skF_3') | ~r1_tarski('#skF_5', A_532) | ~r1_tarski(A_532, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_8263])).
% 19.45/11.24  tff(c_41363, plain, (![A_2229, C_2230]: (m1_connsp_2(k2_xboole_0(A_2229, C_2230), '#skF_2', '#skF_3') | ~r1_tarski('#skF_5', k2_xboole_0(A_2229, C_2230)) | ~r1_tarski(C_2230, u1_struct_0('#skF_2')) | ~r1_tarski(A_2229, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_8295])).
% 19.45/11.24  tff(c_71, plain, (![A_64, B_65, C_66]: (k4_subset_1(A_64, B_65, C_66)=k2_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.45/11.24  tff(c_90, plain, (![B_70]: (k4_subset_1(u1_struct_0('#skF_2'), B_70, '#skF_5')=k2_xboole_0(B_70, '#skF_5') | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_71])).
% 19.45/11.24  tff(c_102, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_90])).
% 19.45/11.24  tff(c_26, plain, (~m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.45/11.24  tff(c_104, plain, (~m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_26])).
% 19.45/11.24  tff(c_41376, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_41363, c_104])).
% 19.45/11.24  tff(c_41399, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_51, c_41376])).
% 19.45/11.24  tff(c_41402, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_41399])).
% 19.45/11.24  tff(c_41406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_41402])).
% 19.45/11.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.45/11.24  
% 19.45/11.24  Inference rules
% 19.45/11.24  ----------------------
% 19.45/11.24  #Ref     : 0
% 19.45/11.24  #Sup     : 9800
% 19.45/11.24  #Fact    : 0
% 19.45/11.24  #Define  : 0
% 19.45/11.24  #Split   : 72
% 19.45/11.24  #Chain   : 0
% 19.45/11.24  #Close   : 0
% 19.45/11.24  
% 19.45/11.24  Ordering : KBO
% 19.45/11.24  
% 19.45/11.24  Simplification rules
% 19.45/11.24  ----------------------
% 19.45/11.24  #Subsume      : 5797
% 19.45/11.24  #Demod        : 1944
% 19.45/11.24  #Tautology    : 1170
% 19.45/11.24  #SimpNegUnit  : 198
% 19.45/11.24  #BackRed      : 2
% 19.45/11.24  
% 19.45/11.24  #Partial instantiations: 0
% 19.45/11.24  #Strategies tried      : 1
% 19.45/11.24  
% 19.45/11.24  Timing (in seconds)
% 19.45/11.24  ----------------------
% 19.45/11.24  Preprocessing        : 0.32
% 19.45/11.24  Parsing              : 0.17
% 19.45/11.24  CNF conversion       : 0.03
% 19.45/11.24  Main loop            : 10.14
% 19.45/11.24  Inferencing          : 1.65
% 19.45/11.24  Reduction            : 2.71
% 19.45/11.24  Demodulation         : 1.87
% 19.45/11.24  BG Simplification    : 0.12
% 19.45/11.24  Subsumption          : 5.17
% 19.45/11.24  Abstraction          : 0.23
% 19.45/11.24  MUC search           : 0.00
% 19.45/11.24  Cooper               : 0.00
% 19.45/11.24  Total                : 10.49
% 19.45/11.24  Index Insertion      : 0.00
% 19.45/11.24  Index Deletion       : 0.00
% 19.45/11.24  Index Matching       : 0.00
% 19.45/11.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
