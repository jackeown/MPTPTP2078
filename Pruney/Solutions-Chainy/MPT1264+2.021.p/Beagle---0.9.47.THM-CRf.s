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
% DateTime   : Thu Dec  3 10:21:41 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 232 expanded)
%              Number of leaves         :   35 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 ( 543 expanded)
%              Number of equality atoms :   30 ( 116 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_91,axiom,(
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

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_55,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_64,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_67,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_38])).

tff(c_83,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    ! [B_50] : k9_subset_1(k2_struct_0('#skF_2'),B_50,'#skF_3') = k3_xboole_0(B_50,'#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_83])).

tff(c_30,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_65,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_102,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_65])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_229,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden('#skF_1'(A_72,B_73,C_74),B_73)
      | r1_tarski(B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_328,plain,(
    ! [A_83,B_84,C_85,A_86] :
      ( r2_hidden('#skF_1'(A_83,B_84,C_85),A_86)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_86))
      | r1_tarski(B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_229,c_8])).

tff(c_12,plain,(
    ! [A_12,B_13,C_17] :
      ( ~ r2_hidden('#skF_1'(A_12,B_13,C_17),C_17)
      | r1_tarski(B_13,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_337,plain,(
    ! [B_87,A_88,A_89] :
      ( ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | r1_tarski(B_87,A_88)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_328,c_12])).

tff(c_349,plain,(
    ! [A_89] :
      ( r1_tarski('#skF_4',k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(A_89))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_66,c_337])).

tff(c_381,plain,(
    ! [A_95] :
      ( ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(A_95))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_95)) ) ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_385,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_43,c_381])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_385])).

tff(c_390,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_394,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_390,c_2])).

tff(c_32,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_92,plain,(
    ! [A_4,B_50] : k9_subset_1(A_4,B_50,A_4) = k3_xboole_0(B_50,A_4) ),
    inference(resolution,[status(thm)],[c_43,c_83])).

tff(c_36,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_121,plain,(
    ! [A_56,B_57] :
      ( k2_pre_topc(A_56,B_57) = k2_struct_0(A_56)
      | ~ v1_tops_1(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_124,plain,(
    ! [B_57] :
      ( k2_pre_topc('#skF_2',B_57) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_57,'#skF_2')
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_121])).

tff(c_179,plain,(
    ! [B_63] :
      ( k2_pre_topc('#skF_2',B_63) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_63,'#skF_2')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_124])).

tff(c_182,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_179])).

tff(c_192,plain,(
    k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_182])).

tff(c_260,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_pre_topc(A_78,k9_subset_1(u1_struct_0(A_78),B_79,k2_pre_topc(A_78,C_80))) = k2_pre_topc(A_78,k9_subset_1(u1_struct_0(A_78),B_79,C_80))
      | ~ v3_pre_topc(B_79,A_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_275,plain,(
    ! [B_79] :
      ( k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_79,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_79,'#skF_3'))
      | ~ v3_pre_topc(B_79,'#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_260])).

tff(c_294,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_2',k3_xboole_0(B_82,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0(B_82,'#skF_3'))
      | ~ v3_pre_topc(B_82,'#skF_2')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_64,c_67,c_64,c_90,c_92,c_64,c_64,c_275])).

tff(c_304,plain,
    ( k2_pre_topc('#skF_2',k3_xboole_0('#skF_4',k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_294])).

tff(c_314,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4',k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_304])).

tff(c_399,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_314])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.59/1.35  
% 2.59/1.35  %Foreground sorts:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Background operators:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Foreground operators:
% 2.59/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.35  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.59/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.59/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.59/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.59/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.59/1.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.59/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.59/1.35  
% 2.59/1.37  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 2.59/1.37  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.59/1.37  tff(f_64, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.59/1.37  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.59/1.37  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.59/1.37  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.59/1.37  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.59/1.37  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.59/1.37  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.59/1.37  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.59/1.37  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 2.59/1.37  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.59/1.37  tff(c_22, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.59/1.37  tff(c_55, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.37  tff(c_60, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_22, c_55])).
% 2.59/1.37  tff(c_64, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_60])).
% 2.59/1.37  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.59/1.37  tff(c_67, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_38])).
% 2.59/1.37  tff(c_83, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.37  tff(c_90, plain, (![B_50]: (k9_subset_1(k2_struct_0('#skF_2'), B_50, '#skF_3')=k3_xboole_0(B_50, '#skF_3'))), inference(resolution, [status(thm)], [c_67, c_83])).
% 2.59/1.37  tff(c_30, plain, (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.59/1.37  tff(c_65, plain, (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 2.59/1.37  tff(c_102, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_65])).
% 2.59/1.37  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.59/1.37  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34])).
% 2.59/1.37  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.37  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.59/1.37  tff(c_43, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.59/1.37  tff(c_229, plain, (![A_72, B_73, C_74]: (r2_hidden('#skF_1'(A_72, B_73, C_74), B_73) | r1_tarski(B_73, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.59/1.37  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.59/1.37  tff(c_328, plain, (![A_83, B_84, C_85, A_86]: (r2_hidden('#skF_1'(A_83, B_84, C_85), A_86) | ~m1_subset_1(B_84, k1_zfmisc_1(A_86)) | r1_tarski(B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_229, c_8])).
% 2.59/1.37  tff(c_12, plain, (![A_12, B_13, C_17]: (~r2_hidden('#skF_1'(A_12, B_13, C_17), C_17) | r1_tarski(B_13, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.59/1.37  tff(c_337, plain, (![B_87, A_88, A_89]: (~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | r1_tarski(B_87, A_88) | ~m1_subset_1(A_88, k1_zfmisc_1(A_89)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_328, c_12])).
% 2.59/1.37  tff(c_349, plain, (![A_89]: (r1_tarski('#skF_4', k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(A_89)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_66, c_337])).
% 2.59/1.37  tff(c_381, plain, (![A_95]: (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(A_95)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_95)))), inference(splitLeft, [status(thm)], [c_349])).
% 2.59/1.37  tff(c_385, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_43, c_381])).
% 2.59/1.37  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_385])).
% 2.59/1.37  tff(c_390, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_349])).
% 2.59/1.37  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.37  tff(c_394, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_390, c_2])).
% 2.59/1.37  tff(c_32, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.59/1.37  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.59/1.37  tff(c_92, plain, (![A_4, B_50]: (k9_subset_1(A_4, B_50, A_4)=k3_xboole_0(B_50, A_4))), inference(resolution, [status(thm)], [c_43, c_83])).
% 2.59/1.37  tff(c_36, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.59/1.37  tff(c_121, plain, (![A_56, B_57]: (k2_pre_topc(A_56, B_57)=k2_struct_0(A_56) | ~v1_tops_1(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.59/1.37  tff(c_124, plain, (![B_57]: (k2_pre_topc('#skF_2', B_57)=k2_struct_0('#skF_2') | ~v1_tops_1(B_57, '#skF_2') | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_121])).
% 2.59/1.37  tff(c_179, plain, (![B_63]: (k2_pre_topc('#skF_2', B_63)=k2_struct_0('#skF_2') | ~v1_tops_1(B_63, '#skF_2') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_124])).
% 2.59/1.37  tff(c_182, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_67, c_179])).
% 2.59/1.37  tff(c_192, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_182])).
% 2.59/1.37  tff(c_260, plain, (![A_78, B_79, C_80]: (k2_pre_topc(A_78, k9_subset_1(u1_struct_0(A_78), B_79, k2_pre_topc(A_78, C_80)))=k2_pre_topc(A_78, k9_subset_1(u1_struct_0(A_78), B_79, C_80)) | ~v3_pre_topc(B_79, A_78) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.59/1.37  tff(c_275, plain, (![B_79]: (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_79, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_79, '#skF_3')) | ~v3_pre_topc(B_79, '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_192, c_260])).
% 2.59/1.37  tff(c_294, plain, (![B_82]: (k2_pre_topc('#skF_2', k3_xboole_0(B_82, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0(B_82, '#skF_3')) | ~v3_pre_topc(B_82, '#skF_2') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_64, c_67, c_64, c_90, c_92, c_64, c_64, c_275])).
% 2.59/1.37  tff(c_304, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_294])).
% 2.59/1.37  tff(c_314, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_304])).
% 2.59/1.37  tff(c_399, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_314])).
% 2.59/1.37  tff(c_401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_399])).
% 2.59/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.37  
% 2.59/1.37  Inference rules
% 2.59/1.37  ----------------------
% 2.59/1.37  #Ref     : 0
% 2.59/1.37  #Sup     : 75
% 2.59/1.37  #Fact    : 0
% 2.59/1.37  #Define  : 0
% 2.59/1.37  #Split   : 6
% 2.59/1.37  #Chain   : 0
% 2.59/1.37  #Close   : 0
% 2.59/1.37  
% 2.59/1.37  Ordering : KBO
% 2.59/1.37  
% 2.59/1.37  Simplification rules
% 2.59/1.37  ----------------------
% 2.59/1.37  #Subsume      : 2
% 2.59/1.37  #Demod        : 44
% 2.59/1.37  #Tautology    : 30
% 2.59/1.37  #SimpNegUnit  : 5
% 2.59/1.37  #BackRed      : 5
% 2.59/1.37  
% 2.59/1.37  #Partial instantiations: 0
% 2.59/1.37  #Strategies tried      : 1
% 2.59/1.37  
% 2.59/1.37  Timing (in seconds)
% 2.59/1.37  ----------------------
% 2.59/1.37  Preprocessing        : 0.32
% 2.59/1.37  Parsing              : 0.17
% 2.59/1.37  CNF conversion       : 0.02
% 2.59/1.37  Main loop            : 0.27
% 2.59/1.37  Inferencing          : 0.10
% 2.59/1.37  Reduction            : 0.08
% 2.59/1.37  Demodulation         : 0.06
% 2.59/1.37  BG Simplification    : 0.02
% 2.59/1.37  Subsumption          : 0.05
% 2.59/1.37  Abstraction          : 0.02
% 2.59/1.37  MUC search           : 0.00
% 2.59/1.37  Cooper               : 0.00
% 2.59/1.37  Total                : 0.63
% 2.59/1.37  Index Insertion      : 0.00
% 2.59/1.37  Index Deletion       : 0.00
% 2.59/1.37  Index Matching       : 0.00
% 2.59/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
