%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:49 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 116 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 353 expanded)
%              Number of equality atoms :   21 (  51 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_56,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_305,plain,(
    ! [B_70,A_71] :
      ( v2_tops_1(B_70,A_71)
      | k1_tops_1(A_71,B_70) != k1_xboole_0
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_315,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_305])).

tff(c_324,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_315])).

tff(c_325,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_324])).

tff(c_113,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tops_1(A_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_118,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_125,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_118])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_327,plain,(
    ! [A_72,B_73] :
      ( v3_pre_topc(k1_tops_1(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_334,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_327])).

tff(c_342,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_334])).

tff(c_193,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k1_tops_1(A_60,B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    ! [C_33] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_33
      | ~ v3_pre_topc(C_33,'#skF_1')
      | ~ r1_tarski(C_33,'#skF_2')
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_162,plain,(
    ! [C_33] :
      ( k1_xboole_0 = C_33
      | ~ v3_pre_topc(C_33,'#skF_1')
      | ~ r1_tarski(C_33,'#skF_2')
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52])).

tff(c_197,plain,(
    ! [B_61] :
      ( k1_tops_1('#skF_1',B_61) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_61),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_61),'#skF_2')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_193,c_162])).

tff(c_422,plain,(
    ! [B_87] :
      ( k1_tops_1('#skF_1',B_87) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_87),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_87),'#skF_2')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_197])).

tff(c_433,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_422])).

tff(c_444,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_342,c_433])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_444])).

tff(c_447,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_448,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_452,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_36])).

tff(c_38,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_450,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_38])).

tff(c_40,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_469,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_40])).

tff(c_577,plain,(
    ! [A_110,B_111] :
      ( k1_tops_1(A_110,B_111) = k1_xboole_0
      | ~ v2_tops_1(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_587,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_577])).

tff(c_598,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_448,c_587])).

tff(c_828,plain,(
    ! [B_134,A_135,C_136] :
      ( r1_tarski(B_134,k1_tops_1(A_135,C_136))
      | ~ r1_tarski(B_134,C_136)
      | ~ v3_pre_topc(B_134,A_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_837,plain,(
    ! [B_134] :
      ( r1_tarski(B_134,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_134,'#skF_2')
      | ~ v3_pre_topc(B_134,'#skF_1')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_828])).

tff(c_850,plain,(
    ! [B_137] :
      ( r1_tarski(B_137,k1_xboole_0)
      | ~ r1_tarski(B_137,'#skF_2')
      | ~ v3_pre_topc(B_137,'#skF_1')
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_598,c_837])).

tff(c_857,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_469,c_850])).

tff(c_874,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_450,c_857])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_453,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(A_88,B_89)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_461,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_453])).

tff(c_474,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_487,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_461,c_474])).

tff(c_884,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_874,c_487])).

tff(c_890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.43  
% 2.74/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.43  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.43  
% 2.74/1.43  %Foreground sorts:
% 2.74/1.43  
% 2.74/1.43  
% 2.74/1.43  %Background operators:
% 2.74/1.43  
% 2.74/1.43  
% 2.74/1.43  %Foreground operators:
% 2.74/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.43  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.74/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.74/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.74/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.43  
% 3.11/1.45  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.11/1.45  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.11/1.45  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.11/1.45  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.11/1.45  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.11/1.45  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.11/1.45  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.11/1.45  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.11/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.11/1.45  tff(c_34, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.45  tff(c_56, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 3.11/1.45  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.45  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.45  tff(c_305, plain, (![B_70, A_71]: (v2_tops_1(B_70, A_71) | k1_tops_1(A_71, B_70)!=k1_xboole_0 | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.11/1.45  tff(c_315, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_305])).
% 3.11/1.45  tff(c_324, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_315])).
% 3.11/1.45  tff(c_325, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_324])).
% 3.11/1.45  tff(c_113, plain, (![A_53, B_54]: (r1_tarski(k1_tops_1(A_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.11/1.45  tff(c_118, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_113])).
% 3.11/1.45  tff(c_125, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_118])).
% 3.11/1.45  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.45  tff(c_327, plain, (![A_72, B_73]: (v3_pre_topc(k1_tops_1(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.11/1.45  tff(c_334, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_327])).
% 3.11/1.45  tff(c_342, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_334])).
% 3.11/1.45  tff(c_193, plain, (![A_60, B_61]: (m1_subset_1(k1_tops_1(A_60, B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.11/1.45  tff(c_52, plain, (![C_33]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_33 | ~v3_pre_topc(C_33, '#skF_1') | ~r1_tarski(C_33, '#skF_2') | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.45  tff(c_162, plain, (![C_33]: (k1_xboole_0=C_33 | ~v3_pre_topc(C_33, '#skF_1') | ~r1_tarski(C_33, '#skF_2') | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_52])).
% 3.11/1.45  tff(c_197, plain, (![B_61]: (k1_tops_1('#skF_1', B_61)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_61), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_61), '#skF_2') | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_193, c_162])).
% 3.11/1.45  tff(c_422, plain, (![B_87]: (k1_tops_1('#skF_1', B_87)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_87), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_87), '#skF_2') | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_197])).
% 3.11/1.45  tff(c_433, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_422])).
% 3.11/1.45  tff(c_444, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_125, c_342, c_433])).
% 3.11/1.45  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_325, c_444])).
% 3.11/1.45  tff(c_447, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 3.11/1.45  tff(c_448, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 3.11/1.45  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.45  tff(c_452, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_36])).
% 3.11/1.45  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.45  tff(c_450, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_38])).
% 3.11/1.45  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.45  tff(c_469, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_40])).
% 3.11/1.45  tff(c_577, plain, (![A_110, B_111]: (k1_tops_1(A_110, B_111)=k1_xboole_0 | ~v2_tops_1(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.11/1.45  tff(c_587, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_577])).
% 3.11/1.45  tff(c_598, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_448, c_587])).
% 3.11/1.45  tff(c_828, plain, (![B_134, A_135, C_136]: (r1_tarski(B_134, k1_tops_1(A_135, C_136)) | ~r1_tarski(B_134, C_136) | ~v3_pre_topc(B_134, A_135) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.11/1.45  tff(c_837, plain, (![B_134]: (r1_tarski(B_134, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_134, '#skF_2') | ~v3_pre_topc(B_134, '#skF_1') | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_828])).
% 3.11/1.45  tff(c_850, plain, (![B_137]: (r1_tarski(B_137, k1_xboole_0) | ~r1_tarski(B_137, '#skF_2') | ~v3_pre_topc(B_137, '#skF_1') | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_598, c_837])).
% 3.11/1.45  tff(c_857, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_469, c_850])).
% 3.11/1.45  tff(c_874, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_452, c_450, c_857])).
% 3.11/1.45  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.11/1.45  tff(c_453, plain, (![A_88, B_89]: (r1_tarski(A_88, B_89) | ~m1_subset_1(A_88, k1_zfmisc_1(B_89)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.11/1.45  tff(c_461, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_8, c_453])).
% 3.11/1.45  tff(c_474, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.45  tff(c_487, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_461, c_474])).
% 3.11/1.45  tff(c_884, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_874, c_487])).
% 3.11/1.45  tff(c_890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_447, c_884])).
% 3.11/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.45  
% 3.11/1.45  Inference rules
% 3.11/1.45  ----------------------
% 3.11/1.45  #Ref     : 0
% 3.11/1.45  #Sup     : 161
% 3.11/1.45  #Fact    : 0
% 3.11/1.45  #Define  : 0
% 3.11/1.45  #Split   : 10
% 3.11/1.45  #Chain   : 0
% 3.11/1.45  #Close   : 0
% 3.11/1.45  
% 3.11/1.45  Ordering : KBO
% 3.11/1.45  
% 3.11/1.45  Simplification rules
% 3.11/1.45  ----------------------
% 3.11/1.45  #Subsume      : 28
% 3.11/1.45  #Demod        : 140
% 3.11/1.45  #Tautology    : 49
% 3.11/1.45  #SimpNegUnit  : 7
% 3.11/1.45  #BackRed      : 1
% 3.11/1.45  
% 3.11/1.45  #Partial instantiations: 0
% 3.11/1.45  #Strategies tried      : 1
% 3.11/1.45  
% 3.11/1.45  Timing (in seconds)
% 3.11/1.45  ----------------------
% 3.11/1.45  Preprocessing        : 0.32
% 3.11/1.45  Parsing              : 0.17
% 3.11/1.45  CNF conversion       : 0.02
% 3.11/1.45  Main loop            : 0.36
% 3.11/1.45  Inferencing          : 0.13
% 3.11/1.45  Reduction            : 0.11
% 3.11/1.45  Demodulation         : 0.07
% 3.11/1.45  BG Simplification    : 0.02
% 3.11/1.45  Subsumption          : 0.08
% 3.11/1.45  Abstraction          : 0.02
% 3.11/1.45  MUC search           : 0.00
% 3.11/1.45  Cooper               : 0.00
% 3.11/1.45  Total                : 0.71
% 3.11/1.45  Index Insertion      : 0.00
% 3.11/1.45  Index Deletion       : 0.00
% 3.11/1.45  Index Matching       : 0.00
% 3.11/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
