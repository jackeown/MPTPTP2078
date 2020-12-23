%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:41 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 (  99 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_42,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_42])).

tff(c_47,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = B_39
      | ~ v4_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_47])).

tff(c_53,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_57,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_14])).

tff(c_61,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k2_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_xboole_0(A_3,B_4)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ! [A_3] :
      ( r1_xboole_0(A_3,k1_relat_1('#skF_4'))
      | ~ r1_xboole_0(A_3,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8])).

tff(c_103,plain,(
    ! [A_47,B_48] :
      ( k7_relat_1(A_47,B_48) = k1_xboole_0
      | ~ r1_xboole_0(B_48,k1_relat_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    ! [A_3] :
      ( k7_relat_1('#skF_4',A_3) = k1_xboole_0
      | ~ v1_relat_1('#skF_4')
      | ~ r1_xboole_0(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70,c_103])).

tff(c_110,plain,(
    ! [A_49] :
      ( k7_relat_1('#skF_4',A_49) = k1_xboole_0
      | ~ r1_xboole_0(A_49,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_114,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_168,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k5_relset_1(A_54,B_55,C_56,D_57) = k7_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_171,plain,(
    ! [D_57] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_57) = k7_relat_1('#skF_4',D_57) ),
    inference(resolution,[status(thm)],[c_28,c_168])).

tff(c_24,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_172,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_24])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:16:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.25  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.08/1.25  
% 2.08/1.25  %Foreground sorts:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Background operators:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Foreground operators:
% 2.08/1.25  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.08/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.08/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.25  
% 2.08/1.26  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.08/1.26  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.08/1.26  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.08/1.26  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.08/1.26  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.08/1.26  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.08/1.26  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.08/1.26  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.08/1.26  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.08/1.26  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.26  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.26  tff(c_30, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.26  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_30])).
% 2.08/1.26  tff(c_42, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.26  tff(c_46, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_42])).
% 2.08/1.26  tff(c_47, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=B_39 | ~v4_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.26  tff(c_50, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_47])).
% 2.08/1.26  tff(c_53, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50])).
% 2.08/1.26  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.08/1.26  tff(c_57, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_53, c_14])).
% 2.08/1.26  tff(c_61, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_57])).
% 2.08/1.26  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.26  tff(c_66, plain, (k2_xboole_0(k1_relat_1('#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_61, c_2])).
% 2.08/1.26  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_xboole_0(A_3, B_4) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.26  tff(c_70, plain, (![A_3]: (r1_xboole_0(A_3, k1_relat_1('#skF_4')) | ~r1_xboole_0(A_3, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_8])).
% 2.08/1.26  tff(c_103, plain, (![A_47, B_48]: (k7_relat_1(A_47, B_48)=k1_xboole_0 | ~r1_xboole_0(B_48, k1_relat_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.26  tff(c_106, plain, (![A_3]: (k7_relat_1('#skF_4', A_3)=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_xboole_0(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_103])).
% 2.08/1.26  tff(c_110, plain, (![A_49]: (k7_relat_1('#skF_4', A_49)=k1_xboole_0 | ~r1_xboole_0(A_49, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_106])).
% 2.08/1.26  tff(c_114, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_110])).
% 2.08/1.26  tff(c_168, plain, (![A_54, B_55, C_56, D_57]: (k5_relset_1(A_54, B_55, C_56, D_57)=k7_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.26  tff(c_171, plain, (![D_57]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_57)=k7_relat_1('#skF_4', D_57))), inference(resolution, [status(thm)], [c_28, c_168])).
% 2.08/1.26  tff(c_24, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.26  tff(c_172, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_171, c_24])).
% 2.08/1.26  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_172])).
% 2.08/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  Inference rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Ref     : 0
% 2.08/1.26  #Sup     : 36
% 2.08/1.26  #Fact    : 0
% 2.08/1.26  #Define  : 0
% 2.08/1.26  #Split   : 1
% 2.08/1.26  #Chain   : 0
% 2.08/1.26  #Close   : 0
% 2.08/1.26  
% 2.08/1.26  Ordering : KBO
% 2.08/1.26  
% 2.08/1.26  Simplification rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Subsume      : 0
% 2.08/1.26  #Demod        : 10
% 2.08/1.26  #Tautology    : 20
% 2.08/1.26  #SimpNegUnit  : 0
% 2.08/1.26  #BackRed      : 1
% 2.08/1.26  
% 2.08/1.26  #Partial instantiations: 0
% 2.08/1.26  #Strategies tried      : 1
% 2.08/1.26  
% 2.08/1.26  Timing (in seconds)
% 2.08/1.26  ----------------------
% 2.08/1.26  Preprocessing        : 0.32
% 2.08/1.26  Parsing              : 0.17
% 2.08/1.26  CNF conversion       : 0.02
% 2.08/1.26  Main loop            : 0.16
% 2.08/1.26  Inferencing          : 0.06
% 2.08/1.26  Reduction            : 0.05
% 2.08/1.26  Demodulation         : 0.03
% 2.08/1.26  BG Simplification    : 0.01
% 2.08/1.26  Subsumption          : 0.02
% 2.08/1.26  Abstraction          : 0.01
% 2.08/1.26  MUC search           : 0.00
% 2.08/1.26  Cooper               : 0.00
% 2.08/1.26  Total                : 0.51
% 2.08/1.26  Index Insertion      : 0.00
% 2.08/1.26  Index Deletion       : 0.00
% 2.08/1.26  Index Matching       : 0.00
% 2.08/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
