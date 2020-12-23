%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:40 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 175 expanded)
%              Number of leaves         :   26 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 500 expanded)
%              Number of equality atoms :   30 (  85 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_98,plain,(
    ! [A_41,B_42,C_43] :
      ( k9_subset_1(A_41,B_42,C_43) = k3_xboole_0(B_42,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_2') = k3_xboole_0(B_42,'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_24,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_108,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_24])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_39,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_48,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_47,c_48])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_146,plain,(
    ! [B_48,B_49,A_50] :
      ( k9_subset_1(B_48,B_49,A_50) = k3_xboole_0(B_49,A_50)
      | ~ r1_tarski(A_50,B_48) ) ),
    inference(resolution,[status(thm)],[c_14,c_98])).

tff(c_157,plain,(
    ! [B_2,B_49] : k9_subset_1(B_2,B_49,B_2) = k3_xboole_0(B_49,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_30,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_210,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_tops_1(C_58,A_59)
      | ~ r1_tarski(B_60,C_58)
      | ~ v1_tops_1(B_60,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_244,plain,(
    ! [A_64] :
      ( v1_tops_1(u1_struct_0('#skF_1'),A_64)
      | ~ v1_tops_1('#skF_2',A_64)
      | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_46,c_210])).

tff(c_254,plain,(
    ! [A_66] :
      ( v1_tops_1(u1_struct_0('#skF_1'),A_66)
      | ~ v1_tops_1('#skF_2',A_66)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ r1_tarski(u1_struct_0('#skF_1'),u1_struct_0(A_66)) ) ),
    inference(resolution,[status(thm)],[c_14,c_244])).

tff(c_258,plain,
    ( v1_tops_1(u1_struct_0('#skF_1'),'#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_261,plain,(
    v1_tops_1(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_258])).

tff(c_158,plain,(
    ! [A_51,B_52] :
      ( k2_pre_topc(A_51,B_52) = k2_struct_0(A_51)
      | ~ v1_tops_1(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_190,plain,(
    ! [A_55,A_56] :
      ( k2_pre_topc(A_55,A_56) = k2_struct_0(A_55)
      | ~ v1_tops_1(A_56,A_55)
      | ~ l1_pre_topc(A_55)
      | ~ r1_tarski(A_56,u1_struct_0(A_55)) ) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_208,plain,(
    ! [A_55] :
      ( k2_pre_topc(A_55,u1_struct_0(A_55)) = k2_struct_0(A_55)
      | ~ v1_tops_1(u1_struct_0(A_55),A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_190])).

tff(c_264,plain,
    ( k2_pre_topc('#skF_1',u1_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_261,c_208])).

tff(c_267,plain,(
    k2_pre_topc('#skF_1',u1_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_264])).

tff(c_280,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_pre_topc(A_68,k9_subset_1(u1_struct_0(A_68),B_69,k2_pre_topc(A_68,C_70))) = k2_pre_topc(A_68,k9_subset_1(u1_struct_0(A_68),B_69,C_70))
      | ~ v3_pre_topc(B_69,A_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_295,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_69,u1_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_69,k2_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_280])).

tff(c_302,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_69,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_69,u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_157,c_295])).

tff(c_338,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_341,plain,(
    ~ r1_tarski(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_338])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_341])).

tff(c_386,plain,(
    ! [B_78] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_78,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_78,u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_78,'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_165,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_158])).

tff(c_172,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_165])).

tff(c_298,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_69,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_69,'#skF_2'))
      | ~ v3_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_280])).

tff(c_304,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_69,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_69,'#skF_2'))
      | ~ v3_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_106,c_298])).

tff(c_410,plain,(
    ! [B_79] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_79,u1_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_79,'#skF_2'))
      | ~ v3_pre_topc(B_79,'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_79,'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_304])).

tff(c_419,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',u1_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_410])).

tff(c_429,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_58,c_419])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.36  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.36  
% 2.61/1.36  %Foreground sorts:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Background operators:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Foreground operators:
% 2.61/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.36  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.61/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.61/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.61/1.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.61/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.61/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.36  
% 2.73/1.38  tff(f_97, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 2.73/1.38  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.73/1.38  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.73/1.38  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.73/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.38  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 2.73/1.38  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.73/1.38  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 2.73/1.38  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.38  tff(c_98, plain, (![A_41, B_42, C_43]: (k9_subset_1(A_41, B_42, C_43)=k3_xboole_0(B_42, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.38  tff(c_106, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_2')=k3_xboole_0(B_42, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_98])).
% 2.73/1.38  tff(c_24, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.38  tff(c_108, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_24])).
% 2.73/1.38  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.38  tff(c_26, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.38  tff(c_39, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.38  tff(c_47, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_39])).
% 2.73/1.38  tff(c_48, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.38  tff(c_58, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_47, c_48])).
% 2.73/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.38  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.38  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.38  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.38  tff(c_146, plain, (![B_48, B_49, A_50]: (k9_subset_1(B_48, B_49, A_50)=k3_xboole_0(B_49, A_50) | ~r1_tarski(A_50, B_48))), inference(resolution, [status(thm)], [c_14, c_98])).
% 2.73/1.38  tff(c_157, plain, (![B_2, B_49]: (k9_subset_1(B_2, B_49, B_2)=k3_xboole_0(B_49, B_2))), inference(resolution, [status(thm)], [c_6, c_146])).
% 2.73/1.38  tff(c_30, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.38  tff(c_46, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_39])).
% 2.73/1.38  tff(c_210, plain, (![C_58, A_59, B_60]: (v1_tops_1(C_58, A_59) | ~r1_tarski(B_60, C_58) | ~v1_tops_1(B_60, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.38  tff(c_244, plain, (![A_64]: (v1_tops_1(u1_struct_0('#skF_1'), A_64) | ~v1_tops_1('#skF_2', A_64) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_46, c_210])).
% 2.73/1.38  tff(c_254, plain, (![A_66]: (v1_tops_1(u1_struct_0('#skF_1'), A_66) | ~v1_tops_1('#skF_2', A_66) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~r1_tarski(u1_struct_0('#skF_1'), u1_struct_0(A_66)))), inference(resolution, [status(thm)], [c_14, c_244])).
% 2.73/1.38  tff(c_258, plain, (v1_tops_1(u1_struct_0('#skF_1'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_254])).
% 2.73/1.38  tff(c_261, plain, (v1_tops_1(u1_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_258])).
% 2.73/1.38  tff(c_158, plain, (![A_51, B_52]: (k2_pre_topc(A_51, B_52)=k2_struct_0(A_51) | ~v1_tops_1(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.38  tff(c_190, plain, (![A_55, A_56]: (k2_pre_topc(A_55, A_56)=k2_struct_0(A_55) | ~v1_tops_1(A_56, A_55) | ~l1_pre_topc(A_55) | ~r1_tarski(A_56, u1_struct_0(A_55)))), inference(resolution, [status(thm)], [c_14, c_158])).
% 2.73/1.38  tff(c_208, plain, (![A_55]: (k2_pre_topc(A_55, u1_struct_0(A_55))=k2_struct_0(A_55) | ~v1_tops_1(u1_struct_0(A_55), A_55) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_6, c_190])).
% 2.73/1.38  tff(c_264, plain, (k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_261, c_208])).
% 2.73/1.38  tff(c_267, plain, (k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_264])).
% 2.73/1.38  tff(c_280, plain, (![A_68, B_69, C_70]: (k2_pre_topc(A_68, k9_subset_1(u1_struct_0(A_68), B_69, k2_pre_topc(A_68, C_70)))=k2_pre_topc(A_68, k9_subset_1(u1_struct_0(A_68), B_69, C_70)) | ~v3_pre_topc(B_69, A_68) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.73/1.38  tff(c_295, plain, (![B_69]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_69, u1_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_69, k2_struct_0('#skF_1'))) | ~v3_pre_topc(B_69, '#skF_1') | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_267, c_280])).
% 2.73/1.38  tff(c_302, plain, (![B_69]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_69, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_69, u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_69, '#skF_1') | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_157, c_295])).
% 2.73/1.38  tff(c_338, plain, (~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_302])).
% 2.73/1.38  tff(c_341, plain, (~r1_tarski(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_338])).
% 2.73/1.38  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_341])).
% 2.73/1.38  tff(c_386, plain, (![B_78]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_78, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_78, u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_78, '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_302])).
% 2.73/1.38  tff(c_165, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_158])).
% 2.73/1.38  tff(c_172, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_165])).
% 2.73/1.38  tff(c_298, plain, (![B_69]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_69, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_69, '#skF_2')) | ~v3_pre_topc(B_69, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_280])).
% 2.73/1.38  tff(c_304, plain, (![B_69]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_69, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_69, '#skF_2')) | ~v3_pre_topc(B_69, '#skF_1') | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_106, c_298])).
% 2.73/1.38  tff(c_410, plain, (![B_79]: (k2_pre_topc('#skF_1', k3_xboole_0(B_79, u1_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_79, '#skF_2')) | ~v3_pre_topc(B_79, '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_79, '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_386, c_304])).
% 2.73/1.38  tff(c_419, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', u1_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_410])).
% 2.73/1.38  tff(c_429, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_58, c_419])).
% 2.73/1.38  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_429])).
% 2.73/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  Inference rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Ref     : 0
% 2.73/1.38  #Sup     : 84
% 2.73/1.38  #Fact    : 0
% 2.73/1.38  #Define  : 0
% 2.73/1.38  #Split   : 4
% 2.73/1.38  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.38  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 4
% 2.73/1.38  #Demod        : 85
% 2.73/1.38  #Tautology    : 38
% 2.73/1.38  #SimpNegUnit  : 4
% 2.73/1.38  #BackRed      : 1
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.73/1.38  Preprocessing        : 0.30
% 2.73/1.38  Parsing              : 0.15
% 2.73/1.38  CNF conversion       : 0.02
% 2.73/1.38  Main loop            : 0.28
% 2.73/1.38  Inferencing          : 0.10
% 2.73/1.38  Reduction            : 0.10
% 2.73/1.38  Demodulation         : 0.07
% 2.73/1.38  BG Simplification    : 0.02
% 2.73/1.38  Subsumption          : 0.05
% 2.73/1.38  Abstraction          : 0.02
% 2.73/1.38  MUC search           : 0.00
% 2.73/1.38  Cooper               : 0.00
% 2.73/1.38  Total                : 0.62
% 2.73/1.38  Index Insertion      : 0.00
% 2.73/1.38  Index Deletion       : 0.00
% 2.73/1.38  Index Matching       : 0.00
% 2.73/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
