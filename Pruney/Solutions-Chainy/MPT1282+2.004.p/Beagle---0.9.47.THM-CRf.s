%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:20 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 189 expanded)
%              Number of leaves         :   22 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 494 expanded)
%              Number of equality atoms :   33 ( 161 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > m1_subset_1 > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v6_tops_1(B,A)
             => ( k2_tops_1(A,B) = k2_tops_1(A,k2_pre_topc(A,B))
                & k2_tops_1(A,k2_pre_topc(A,B)) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_18,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k2_pre_topc(A_1,B_2),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_55,plain,(
    ! [A_24,B_25] :
      ( k1_tops_1(A_24,k2_pre_topc(A_24,B_25)) = B_25
      | ~ v6_tops_1(B_25,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_59,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_63,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_59])).

tff(c_68,plain,(
    ! [B_26,A_27] :
      ( v5_tops_1(B_26,A_27)
      | k2_pre_topc(A_27,k1_tops_1(A_27,B_26)) != B_26
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,
    ( v5_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_68])).

tff(c_73,plain,
    ( v5_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_70])).

tff(c_74,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_87,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_87])).

tff(c_92,plain,(
    v5_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_93,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_121,plain,(
    ! [A_32,B_33] :
      ( k2_tops_1(A_32,k1_tops_1(A_32,B_33)) = k2_tops_1(A_32,B_33)
      | ~ v5_tops_1(B_33,A_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_123,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ v5_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_93,c_121])).

tff(c_130,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_92,c_63,c_123])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_130])).

tff(c_134,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_133,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_139,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_133])).

tff(c_145,plain,(
    ! [A_36,B_37] :
      ( k1_tops_1(A_36,k2_pre_topc(A_36,B_37)) = B_37
      | ~ v6_tops_1(B_37,A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_149,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_145])).

tff(c_153,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_149])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k2_pre_topc(A_20,k2_pre_topc(A_20,B_21)) = k2_pre_topc(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_26])).

tff(c_34,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_140,plain,(
    ! [B_34,A_35] :
      ( v6_tops_1(B_34,A_35)
      | k1_tops_1(A_35,k2_pre_topc(A_35,B_34)) != B_34
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_142,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_140])).

tff(c_144,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_142])).

tff(c_163,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_144])).

tff(c_164,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_167,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_167])).

tff(c_173,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_211,plain,(
    ! [A_42,B_43] :
      ( k7_subset_1(u1_struct_0(A_42),k2_pre_topc(A_42,B_43),k1_tops_1(A_42,B_43)) = k2_tops_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_220,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_211])).

tff(c_227,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_173,c_34,c_134,c_220])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  %$ v6_tops_1 > v5_tops_1 > m1_subset_1 > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.18/1.27  
% 2.18/1.27  %Foreground sorts:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Background operators:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Foreground operators:
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.27  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 2.18/1.27  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.18/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.27  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.18/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.27  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.18/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.27  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.18/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.27  
% 2.18/1.28  tff(f_83, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) => ((k2_tops_1(A, B) = k2_tops_1(A, k2_pre_topc(A, B))) & (k2_tops_1(A, k2_pre_topc(A, B)) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tops_1)).
% 2.18/1.28  tff(f_31, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.18/1.28  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 2.18/1.28  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 2.18/1.28  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 2.18/1.28  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.18/1.28  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.18/1.28  tff(c_18, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.28  tff(c_54, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 2.18/1.28  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.28  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.28  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k2_pre_topc(A_1, B_2), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.28  tff(c_20, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.28  tff(c_55, plain, (![A_24, B_25]: (k1_tops_1(A_24, k2_pre_topc(A_24, B_25))=B_25 | ~v6_tops_1(B_25, A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.28  tff(c_59, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_55])).
% 2.18/1.28  tff(c_63, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_59])).
% 2.18/1.28  tff(c_68, plain, (![B_26, A_27]: (v5_tops_1(B_26, A_27) | k2_pre_topc(A_27, k1_tops_1(A_27, B_26))!=B_26 | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.28  tff(c_70, plain, (v5_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_63, c_68])).
% 2.18/1.28  tff(c_73, plain, (v5_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_70])).
% 2.18/1.28  tff(c_74, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_73])).
% 2.18/1.28  tff(c_87, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_74])).
% 2.18/1.28  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_87])).
% 2.18/1.28  tff(c_92, plain, (v5_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_73])).
% 2.18/1.28  tff(c_93, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_73])).
% 2.18/1.28  tff(c_121, plain, (![A_32, B_33]: (k2_tops_1(A_32, k1_tops_1(A_32, B_33))=k2_tops_1(A_32, B_33) | ~v5_tops_1(B_33, A_32) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.18/1.28  tff(c_123, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~v5_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_93, c_121])).
% 2.18/1.28  tff(c_130, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_92, c_63, c_123])).
% 2.18/1.28  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_130])).
% 2.18/1.28  tff(c_134, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 2.18/1.28  tff(c_133, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_18])).
% 2.18/1.28  tff(c_139, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_133])).
% 2.18/1.28  tff(c_145, plain, (![A_36, B_37]: (k1_tops_1(A_36, k2_pre_topc(A_36, B_37))=B_37 | ~v6_tops_1(B_37, A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.28  tff(c_149, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_145])).
% 2.18/1.28  tff(c_153, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_149])).
% 2.18/1.28  tff(c_26, plain, (![A_20, B_21]: (k2_pre_topc(A_20, k2_pre_topc(A_20, B_21))=k2_pre_topc(A_20, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.28  tff(c_30, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_26])).
% 2.18/1.28  tff(c_34, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 2.18/1.28  tff(c_140, plain, (![B_34, A_35]: (v6_tops_1(B_34, A_35) | k1_tops_1(A_35, k2_pre_topc(A_35, B_34))!=B_34 | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.28  tff(c_142, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_140])).
% 2.18/1.28  tff(c_144, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_142])).
% 2.18/1.28  tff(c_163, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_144])).
% 2.18/1.28  tff(c_164, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_163])).
% 2.18/1.28  tff(c_167, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_164])).
% 2.18/1.28  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_167])).
% 2.18/1.28  tff(c_173, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_163])).
% 2.18/1.28  tff(c_211, plain, (![A_42, B_43]: (k7_subset_1(u1_struct_0(A_42), k2_pre_topc(A_42, B_43), k1_tops_1(A_42, B_43))=k2_tops_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.28  tff(c_220, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_153, c_211])).
% 2.18/1.28  tff(c_227, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_173, c_34, c_134, c_220])).
% 2.18/1.28  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_227])).
% 2.18/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  Inference rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Ref     : 0
% 2.18/1.28  #Sup     : 43
% 2.18/1.28  #Fact    : 0
% 2.18/1.28  #Define  : 0
% 2.18/1.28  #Split   : 6
% 2.18/1.28  #Chain   : 0
% 2.18/1.28  #Close   : 0
% 2.18/1.28  
% 2.18/1.28  Ordering : KBO
% 2.18/1.28  
% 2.18/1.28  Simplification rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Subsume      : 1
% 2.18/1.28  #Demod        : 58
% 2.18/1.28  #Tautology    : 19
% 2.18/1.28  #SimpNegUnit  : 4
% 2.18/1.28  #BackRed      : 0
% 2.18/1.28  
% 2.18/1.28  #Partial instantiations: 0
% 2.18/1.28  #Strategies tried      : 1
% 2.18/1.28  
% 2.18/1.28  Timing (in seconds)
% 2.18/1.28  ----------------------
% 2.18/1.29  Preprocessing        : 0.31
% 2.18/1.29  Parsing              : 0.17
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.21
% 2.18/1.29  Inferencing          : 0.08
% 2.18/1.29  Reduction            : 0.06
% 2.18/1.29  Demodulation         : 0.05
% 2.18/1.29  BG Simplification    : 0.01
% 2.18/1.29  Subsumption          : 0.04
% 2.18/1.29  Abstraction          : 0.01
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.29  Total                : 0.55
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
