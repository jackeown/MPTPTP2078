%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:57 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   55 (  78 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 126 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_51,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_34,plain,
    ( ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_45,plain,(
    ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_38,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden('#skF_3'(A_57,B_58,C_59),B_58)
      | r2_lattice3(A_57,B_58,C_59)
      | ~ m1_subset_1(C_59,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ v1_xboole_0(C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [A_1,A_49] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_49,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_46])).

tff(c_53,plain,(
    ! [A_49] : ~ r2_hidden(A_49,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_80,plain,(
    ! [A_63,C_64] :
      ( r2_lattice3(A_63,k1_xboole_0,C_64)
      | ~ m1_subset_1(C_64,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_63,c_53])).

tff(c_83,plain,
    ( r2_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_80])).

tff(c_86,plain,(
    r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_83])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_86])).

tff(c_89,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_xboole_0('#skF_1'(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_14])).

tff(c_92,plain,(
    ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_112,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_2'(A_78,B_79,C_80),B_79)
      | r1_lattice3(A_78,B_79,C_80)
      | ~ m1_subset_1(C_80,u1_struct_0(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_100,plain,(
    ! [A_1,A_67] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_94])).

tff(c_101,plain,(
    ! [A_67] : ~ r2_hidden(A_67,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_128,plain,(
    ! [A_81,C_82] :
      ( r1_lattice3(A_81,k1_xboole_0,C_82)
      | ~ m1_subset_1(C_82,u1_struct_0(A_81))
      | ~ l1_orders_2(A_81) ) ),
    inference(resolution,[status(thm)],[c_112,c_101])).

tff(c_131,plain,
    ( r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_128])).

tff(c_134,plain,(
    r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_134])).

tff(c_137,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.34  
% 2.15/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.35  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.15/1.35  
% 2.15/1.35  %Foreground sorts:
% 2.15/1.35  
% 2.15/1.35  
% 2.15/1.35  %Background operators:
% 2.15/1.35  
% 2.15/1.35  
% 2.15/1.35  %Foreground operators:
% 2.15/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.35  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.15/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.35  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 2.15/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.35  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.15/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.15/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.15/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.15/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.15/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.35  
% 2.15/1.36  tff(f_89, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 2.15/1.36  tff(f_79, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 2.15/1.36  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.15/1.36  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.15/1.36  tff(f_51, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relset_1)).
% 2.15/1.36  tff(f_65, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 2.15/1.36  tff(c_34, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.15/1.36  tff(c_45, plain, (~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 2.15/1.36  tff(c_38, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.15/1.36  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.15/1.36  tff(c_63, plain, (![A_57, B_58, C_59]: (r2_hidden('#skF_3'(A_57, B_58, C_59), B_58) | r2_lattice3(A_57, B_58, C_59) | ~m1_subset_1(C_59, u1_struct_0(A_57)) | ~l1_orders_2(A_57))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.15/1.36  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.36  tff(c_46, plain, (![C_47, B_48, A_49]: (~v1_xboole_0(C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.15/1.36  tff(c_52, plain, (![A_1, A_49]: (~v1_xboole_0(A_1) | ~r2_hidden(A_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_46])).
% 2.15/1.36  tff(c_53, plain, (![A_49]: (~r2_hidden(A_49, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_52])).
% 2.15/1.36  tff(c_80, plain, (![A_63, C_64]: (r2_lattice3(A_63, k1_xboole_0, C_64) | ~m1_subset_1(C_64, u1_struct_0(A_63)) | ~l1_orders_2(A_63))), inference(resolution, [status(thm)], [c_63, c_53])).
% 2.15/1.36  tff(c_83, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_36, c_80])).
% 2.15/1.36  tff(c_86, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_83])).
% 2.15/1.36  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_86])).
% 2.15/1.36  tff(c_89, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_52])).
% 2.15/1.36  tff(c_14, plain, (![A_8, B_9]: (v1_xboole_0('#skF_1'(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.36  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_14])).
% 2.15/1.36  tff(c_92, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 2.15/1.36  tff(c_112, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_2'(A_78, B_79, C_80), B_79) | r1_lattice3(A_78, B_79, C_80) | ~m1_subset_1(C_80, u1_struct_0(A_78)) | ~l1_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.15/1.36  tff(c_94, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.15/1.36  tff(c_100, plain, (![A_1, A_67]: (~v1_xboole_0(A_1) | ~r2_hidden(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_94])).
% 2.15/1.36  tff(c_101, plain, (![A_67]: (~r2_hidden(A_67, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_100])).
% 2.15/1.36  tff(c_128, plain, (![A_81, C_82]: (r1_lattice3(A_81, k1_xboole_0, C_82) | ~m1_subset_1(C_82, u1_struct_0(A_81)) | ~l1_orders_2(A_81))), inference(resolution, [status(thm)], [c_112, c_101])).
% 2.15/1.36  tff(c_131, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_36, c_128])).
% 2.15/1.36  tff(c_134, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_131])).
% 2.15/1.36  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_134])).
% 2.15/1.36  tff(c_137, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_100])).
% 2.15/1.36  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_14])).
% 2.15/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.36  
% 2.15/1.36  Inference rules
% 2.15/1.36  ----------------------
% 2.15/1.36  #Ref     : 0
% 2.15/1.36  #Sup     : 18
% 2.15/1.36  #Fact    : 0
% 2.15/1.36  #Define  : 0
% 2.15/1.36  #Split   : 3
% 2.15/1.36  #Chain   : 0
% 2.15/1.36  #Close   : 0
% 2.15/1.36  
% 2.15/1.36  Ordering : KBO
% 2.15/1.36  
% 2.15/1.36  Simplification rules
% 2.15/1.36  ----------------------
% 2.15/1.36  #Subsume      : 4
% 2.15/1.36  #Demod        : 2
% 2.15/1.36  #Tautology    : 0
% 2.15/1.36  #SimpNegUnit  : 4
% 2.15/1.36  #BackRed      : 2
% 2.15/1.36  
% 2.15/1.36  #Partial instantiations: 0
% 2.15/1.36  #Strategies tried      : 1
% 2.15/1.36  
% 2.15/1.36  Timing (in seconds)
% 2.15/1.36  ----------------------
% 2.31/1.37  Preprocessing        : 0.32
% 2.31/1.37  Parsing              : 0.17
% 2.31/1.37  CNF conversion       : 0.03
% 2.31/1.37  Main loop            : 0.22
% 2.31/1.37  Inferencing          : 0.09
% 2.31/1.37  Reduction            : 0.06
% 2.31/1.37  Demodulation         : 0.04
% 2.31/1.37  BG Simplification    : 0.01
% 2.31/1.37  Subsumption          : 0.03
% 2.31/1.37  Abstraction          : 0.01
% 2.31/1.37  MUC search           : 0.00
% 2.31/1.37  Cooper               : 0.00
% 2.31/1.37  Total                : 0.57
% 2.31/1.37  Index Insertion      : 0.00
% 2.31/1.37  Index Deletion       : 0.00
% 2.31/1.37  Index Matching       : 0.00
% 2.31/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
