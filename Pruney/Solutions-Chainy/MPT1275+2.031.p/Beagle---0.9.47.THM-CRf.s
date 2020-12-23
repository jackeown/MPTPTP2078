%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:06 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 134 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 324 expanded)
%              Number of equality atoms :   25 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_34,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_81,plain,(
    ! [A_37,B_38] :
      ( k2_pre_topc(A_37,B_38) = B_38
      | ~ v4_pre_topc(B_38,A_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_81])).

tff(c_87,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_84])).

tff(c_104,plain,(
    ! [B_43,A_44] :
      ( v3_tops_1(B_43,A_44)
      | ~ v2_tops_1(k2_pre_topc(A_44,B_43),A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_104])).

tff(c_108,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_106])).

tff(c_109,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_108])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40])).

tff(c_110,plain,(
    ! [B_45,A_46] :
      ( v2_tops_1(B_45,A_46)
      | ~ r1_tarski(B_45,k2_tops_1(A_46,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_112,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_110])).

tff(c_114,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_6,c_112])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_114])).

tff(c_117,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_118,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_145,plain,(
    ! [B_55,A_56] :
      ( v2_tops_1(B_55,A_56)
      | ~ v3_tops_1(B_55,A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_148,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_151,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_118,c_148])).

tff(c_175,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,k2_tops_1(A_66,B_65))
      | ~ v2_tops_1(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_177,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_175])).

tff(c_180,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_151,c_177])).

tff(c_132,plain,(
    ! [A_51,B_52,C_53] :
      ( k7_subset_1(A_51,B_52,C_53) = k4_xboole_0(B_52,C_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [C_53] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_53) = k4_xboole_0('#skF_2',C_53) ),
    inference(resolution,[status(thm)],[c_30,c_132])).

tff(c_152,plain,(
    ! [A_57,B_58] :
      ( k2_pre_topc(A_57,B_58) = B_58
      | ~ v4_pre_topc(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_155,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_152])).

tff(c_158,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_155])).

tff(c_198,plain,(
    ! [A_69,B_70] :
      ( k7_subset_1(u1_struct_0(A_69),k2_pre_topc(A_69,B_70),k1_tops_1(A_69,B_70)) = k2_tops_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_207,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_198])).

tff(c_211,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_135,c_207])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k4_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_215,plain,
    ( k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_126])).

tff(c_222,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_211,c_215])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.24  
% 2.40/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.24  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.40/1.24  
% 2.40/1.24  %Foreground sorts:
% 2.40/1.24  
% 2.40/1.24  
% 2.40/1.24  %Background operators:
% 2.40/1.24  
% 2.40/1.24  
% 2.40/1.24  %Foreground operators:
% 2.40/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.24  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.40/1.24  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.40/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.24  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.40/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.40/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.24  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.40/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.40/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.40/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.40/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.24  
% 2.40/1.26  tff(f_98, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 2.40/1.26  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.40/1.26  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 2.40/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.40/1.26  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 2.40/1.26  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 2.40/1.26  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.40/1.26  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.40/1.26  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.40/1.26  tff(c_34, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.40/1.26  tff(c_44, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.40/1.26  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.40/1.26  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.40/1.26  tff(c_28, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.40/1.26  tff(c_81, plain, (![A_37, B_38]: (k2_pre_topc(A_37, B_38)=B_38 | ~v4_pre_topc(B_38, A_37) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/1.26  tff(c_84, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_81])).
% 2.40/1.26  tff(c_87, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_84])).
% 2.40/1.26  tff(c_104, plain, (![B_43, A_44]: (v3_tops_1(B_43, A_44) | ~v2_tops_1(k2_pre_topc(A_44, B_43), A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.40/1.26  tff(c_106, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_87, c_104])).
% 2.40/1.26  tff(c_108, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_106])).
% 2.40/1.26  tff(c_109, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_108])).
% 2.40/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.26  tff(c_40, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.40/1.26  tff(c_45, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_40])).
% 2.40/1.26  tff(c_110, plain, (![B_45, A_46]: (v2_tops_1(B_45, A_46) | ~r1_tarski(B_45, k2_tops_1(A_46, B_45)) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.40/1.26  tff(c_112, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45, c_110])).
% 2.40/1.26  tff(c_114, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_6, c_112])).
% 2.40/1.26  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_114])).
% 2.40/1.26  tff(c_117, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.40/1.26  tff(c_118, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.40/1.26  tff(c_145, plain, (![B_55, A_56]: (v2_tops_1(B_55, A_56) | ~v3_tops_1(B_55, A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.40/1.26  tff(c_148, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_145])).
% 2.40/1.26  tff(c_151, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_118, c_148])).
% 2.40/1.26  tff(c_175, plain, (![B_65, A_66]: (r1_tarski(B_65, k2_tops_1(A_66, B_65)) | ~v2_tops_1(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.40/1.26  tff(c_177, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_175])).
% 2.40/1.26  tff(c_180, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_151, c_177])).
% 2.40/1.26  tff(c_132, plain, (![A_51, B_52, C_53]: (k7_subset_1(A_51, B_52, C_53)=k4_xboole_0(B_52, C_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.40/1.26  tff(c_135, plain, (![C_53]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_53)=k4_xboole_0('#skF_2', C_53))), inference(resolution, [status(thm)], [c_30, c_132])).
% 2.40/1.26  tff(c_152, plain, (![A_57, B_58]: (k2_pre_topc(A_57, B_58)=B_58 | ~v4_pre_topc(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/1.26  tff(c_155, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_152])).
% 2.40/1.26  tff(c_158, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_155])).
% 2.40/1.26  tff(c_198, plain, (![A_69, B_70]: (k7_subset_1(u1_struct_0(A_69), k2_pre_topc(A_69, B_70), k1_tops_1(A_69, B_70))=k2_tops_1(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.40/1.26  tff(c_207, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_158, c_198])).
% 2.40/1.26  tff(c_211, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_135, c_207])).
% 2.40/1.26  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.26  tff(c_121, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.26  tff(c_126, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k4_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_121])).
% 2.40/1.26  tff(c_215, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_126])).
% 2.40/1.26  tff(c_222, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_211, c_215])).
% 2.40/1.26  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_222])).
% 2.40/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.26  
% 2.40/1.26  Inference rules
% 2.40/1.26  ----------------------
% 2.40/1.26  #Ref     : 0
% 2.40/1.26  #Sup     : 37
% 2.40/1.26  #Fact    : 0
% 2.40/1.26  #Define  : 0
% 2.40/1.26  #Split   : 1
% 2.40/1.26  #Chain   : 0
% 2.40/1.26  #Close   : 0
% 2.40/1.26  
% 2.40/1.26  Ordering : KBO
% 2.40/1.26  
% 2.40/1.26  Simplification rules
% 2.40/1.26  ----------------------
% 2.40/1.26  #Subsume      : 2
% 2.40/1.26  #Demod        : 42
% 2.40/1.26  #Tautology    : 24
% 2.40/1.26  #SimpNegUnit  : 6
% 2.40/1.26  #BackRed      : 0
% 2.40/1.26  
% 2.40/1.26  #Partial instantiations: 0
% 2.40/1.26  #Strategies tried      : 1
% 2.40/1.26  
% 2.40/1.26  Timing (in seconds)
% 2.40/1.26  ----------------------
% 2.40/1.26  Preprocessing        : 0.31
% 2.40/1.26  Parsing              : 0.16
% 2.40/1.26  CNF conversion       : 0.02
% 2.40/1.26  Main loop            : 0.17
% 2.40/1.26  Inferencing          : 0.06
% 2.40/1.26  Reduction            : 0.05
% 2.40/1.26  Demodulation         : 0.04
% 2.40/1.26  BG Simplification    : 0.01
% 2.40/1.26  Subsumption          : 0.03
% 2.40/1.26  Abstraction          : 0.01
% 2.40/1.26  MUC search           : 0.00
% 2.40/1.26  Cooper               : 0.00
% 2.40/1.26  Total                : 0.51
% 2.40/1.26  Index Insertion      : 0.00
% 2.40/1.26  Index Deletion       : 0.00
% 2.40/1.26  Index Matching       : 0.00
% 2.40/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
