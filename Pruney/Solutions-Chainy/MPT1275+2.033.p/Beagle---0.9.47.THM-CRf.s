%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:06 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 102 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 251 expanded)
%              Number of equality atoms :   16 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(c_28,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_37,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_50,plain,(
    ! [A_19,B_20] :
      ( k2_pre_topc(A_19,B_20) = B_20
      | ~ v4_pre_topc(B_20,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_56,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_53])).

tff(c_73,plain,(
    ! [B_25,A_26] :
      ( v3_tops_1(B_25,A_26)
      | ~ v2_tops_1(k2_pre_topc(A_26,B_25),A_26)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_73])).

tff(c_77,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_75])).

tff(c_78,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_34])).

tff(c_85,plain,(
    ! [B_29,A_30] :
      ( v2_tops_1(B_29,A_30)
      | ~ r1_tarski(B_29,k2_tops_1(A_30,B_29))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_87,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_85])).

tff(c_89,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_6,c_87])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_89])).

tff(c_92,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_120,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k2_tops_1(A_37,B_38),B_38)
      | ~ v4_pre_topc(B_38,A_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_120])).

tff(c_125,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_122])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,
    ( k2_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_131,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_128])).

tff(c_93,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_103,plain,(
    ! [A_33,B_34] :
      ( k2_pre_topc(A_33,B_34) = B_34
      | ~ v4_pre_topc(B_34,A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_103])).

tff(c_109,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_106])).

tff(c_114,plain,(
    ! [A_35,B_36] :
      ( v2_tops_1(k2_pre_topc(A_35,B_36),A_35)
      | ~ v3_tops_1(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_119,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_93,c_109,c_116])).

tff(c_137,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(B_43,k2_tops_1(A_44,B_43))
      | ~ v2_tops_1(B_43,A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_139,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_137])).

tff(c_142,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_119,c_139])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.99/1.24  
% 1.99/1.24  %Foreground sorts:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Background operators:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Foreground operators:
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.24  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 1.99/1.24  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.99/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.99/1.24  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.99/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.99/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.99/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.24  
% 1.99/1.26  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 1.99/1.26  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 1.99/1.26  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 1.99/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.99/1.26  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 1.99/1.26  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 1.99/1.26  tff(c_28, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.99/1.26  tff(c_37, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 1.99/1.26  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.99/1.26  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.99/1.26  tff(c_22, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.99/1.26  tff(c_50, plain, (![A_19, B_20]: (k2_pre_topc(A_19, B_20)=B_20 | ~v4_pre_topc(B_20, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.99/1.26  tff(c_53, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_50])).
% 1.99/1.26  tff(c_56, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_53])).
% 1.99/1.26  tff(c_73, plain, (![B_25, A_26]: (v3_tops_1(B_25, A_26) | ~v2_tops_1(k2_pre_topc(A_26, B_25), A_26) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.99/1.26  tff(c_75, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_73])).
% 1.99/1.26  tff(c_77, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_75])).
% 1.99/1.26  tff(c_78, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_37, c_77])).
% 1.99/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.26  tff(c_34, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.99/1.26  tff(c_38, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_37, c_34])).
% 1.99/1.26  tff(c_85, plain, (![B_29, A_30]: (v2_tops_1(B_29, A_30) | ~r1_tarski(B_29, k2_tops_1(A_30, B_29)) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.26  tff(c_87, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_85])).
% 1.99/1.26  tff(c_89, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_6, c_87])).
% 1.99/1.26  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_89])).
% 1.99/1.26  tff(c_92, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 1.99/1.26  tff(c_120, plain, (![A_37, B_38]: (r1_tarski(k2_tops_1(A_37, B_38), B_38) | ~v4_pre_topc(B_38, A_37) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.99/1.26  tff(c_122, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_120])).
% 1.99/1.26  tff(c_125, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_122])).
% 1.99/1.26  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.26  tff(c_128, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_125, c_2])).
% 1.99/1.26  tff(c_131, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_92, c_128])).
% 1.99/1.26  tff(c_93, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 1.99/1.26  tff(c_103, plain, (![A_33, B_34]: (k2_pre_topc(A_33, B_34)=B_34 | ~v4_pre_topc(B_34, A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.99/1.26  tff(c_106, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_103])).
% 1.99/1.26  tff(c_109, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_106])).
% 1.99/1.26  tff(c_114, plain, (![A_35, B_36]: (v2_tops_1(k2_pre_topc(A_35, B_36), A_35) | ~v3_tops_1(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.99/1.26  tff(c_116, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_114])).
% 1.99/1.26  tff(c_119, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_93, c_109, c_116])).
% 1.99/1.26  tff(c_137, plain, (![B_43, A_44]: (r1_tarski(B_43, k2_tops_1(A_44, B_43)) | ~v2_tops_1(B_43, A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.26  tff(c_139, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_137])).
% 1.99/1.26  tff(c_142, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_119, c_139])).
% 1.99/1.26  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_142])).
% 1.99/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.26  
% 1.99/1.26  Inference rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Ref     : 0
% 1.99/1.26  #Sup     : 20
% 1.99/1.26  #Fact    : 0
% 1.99/1.26  #Define  : 0
% 1.99/1.26  #Split   : 1
% 1.99/1.26  #Chain   : 0
% 1.99/1.26  #Close   : 0
% 1.99/1.26  
% 1.99/1.26  Ordering : KBO
% 1.99/1.26  
% 1.99/1.26  Simplification rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Subsume      : 2
% 1.99/1.26  #Demod        : 33
% 1.99/1.26  #Tautology    : 14
% 1.99/1.26  #SimpNegUnit  : 6
% 1.99/1.26  #BackRed      : 0
% 1.99/1.26  
% 1.99/1.26  #Partial instantiations: 0
% 1.99/1.26  #Strategies tried      : 1
% 1.99/1.26  
% 1.99/1.26  Timing (in seconds)
% 1.99/1.26  ----------------------
% 1.99/1.26  Preprocessing        : 0.31
% 1.99/1.26  Parsing              : 0.18
% 1.99/1.26  CNF conversion       : 0.02
% 1.99/1.26  Main loop            : 0.15
% 1.99/1.26  Inferencing          : 0.05
% 1.99/1.26  Reduction            : 0.05
% 1.99/1.26  Demodulation         : 0.04
% 1.99/1.26  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.02
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.49
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
