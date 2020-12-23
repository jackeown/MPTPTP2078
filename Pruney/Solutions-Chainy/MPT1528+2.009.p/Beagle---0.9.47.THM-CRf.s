%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:57 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 120 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_73,axiom,(
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

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_59,axiom,(
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

tff(c_28,plain,
    ( ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_55,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_3'(A_49,B_50,C_51),B_50)
      | r2_lattice3(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [A_3,A_40] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_40,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_44,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_87,plain,(
    ! [A_55,C_56] :
      ( r2_lattice3(A_55,k1_xboole_0,C_56)
      | ~ m1_subset_1(C_56,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(resolution,[status(thm)],[c_55,c_44])).

tff(c_90,plain,
    ( r2_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_87])).

tff(c_93,plain,(
    r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_90])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_93])).

tff(c_96,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_2,plain,(
    ! [A_1] : v1_xboole_0('#skF_1'(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2])).

tff(c_99,plain,(
    ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_143,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_2'(A_76,B_77,C_78),B_77)
      | r1_lattice3(A_76,B_77,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_76))
      | ~ l1_orders_2(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_3,A_59] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_59,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_108,plain,(
    ! [A_59] : ~ r2_hidden(A_59,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_159,plain,(
    ! [A_79,C_80] :
      ( r1_lattice3(A_79,k1_xboole_0,C_80)
      | ~ m1_subset_1(C_80,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79) ) ),
    inference(resolution,[status(thm)],[c_143,c_108])).

tff(c_162,plain,
    ( r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_159])).

tff(c_165,plain,(
    r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_162])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_165])).

tff(c_168,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:28:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.89/1.21  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.89/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.21  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.89/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.21  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 1.89/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.21  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.89/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.21  
% 1.89/1.22  tff(f_83, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 1.89/1.22  tff(f_73, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 1.89/1.22  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.89/1.22  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.89/1.22  tff(f_30, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 1.89/1.22  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 1.89/1.22  tff(c_28, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.89/1.22  tff(c_36, plain, (~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_28])).
% 1.89/1.22  tff(c_32, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.89/1.22  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.89/1.22  tff(c_55, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_3'(A_49, B_50, C_51), B_50) | r2_lattice3(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.89/1.22  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.22  tff(c_37, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.22  tff(c_43, plain, (![A_3, A_40]: (~v1_xboole_0(A_3) | ~r2_hidden(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_37])).
% 1.89/1.22  tff(c_44, plain, (![A_40]: (~r2_hidden(A_40, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_43])).
% 1.89/1.22  tff(c_87, plain, (![A_55, C_56]: (r2_lattice3(A_55, k1_xboole_0, C_56) | ~m1_subset_1(C_56, u1_struct_0(A_55)) | ~l1_orders_2(A_55))), inference(resolution, [status(thm)], [c_55, c_44])).
% 1.89/1.22  tff(c_90, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_30, c_87])).
% 1.89/1.22  tff(c_93, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_90])).
% 1.89/1.22  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_93])).
% 1.89/1.22  tff(c_96, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_43])).
% 1.89/1.22  tff(c_2, plain, (![A_1]: (v1_xboole_0('#skF_1'(A_1)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.89/1.22  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_2])).
% 1.89/1.22  tff(c_99, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 1.89/1.22  tff(c_143, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_2'(A_76, B_77, C_78), B_77) | r1_lattice3(A_76, B_77, C_78) | ~m1_subset_1(C_78, u1_struct_0(A_76)) | ~l1_orders_2(A_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.89/1.22  tff(c_101, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.22  tff(c_107, plain, (![A_3, A_59]: (~v1_xboole_0(A_3) | ~r2_hidden(A_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_101])).
% 1.89/1.22  tff(c_108, plain, (![A_59]: (~r2_hidden(A_59, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_107])).
% 1.89/1.22  tff(c_159, plain, (![A_79, C_80]: (r1_lattice3(A_79, k1_xboole_0, C_80) | ~m1_subset_1(C_80, u1_struct_0(A_79)) | ~l1_orders_2(A_79))), inference(resolution, [status(thm)], [c_143, c_108])).
% 1.89/1.22  tff(c_162, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_30, c_159])).
% 1.89/1.22  tff(c_165, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_162])).
% 1.89/1.22  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_165])).
% 1.89/1.22  tff(c_168, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_107])).
% 1.89/1.22  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_2])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 0
% 1.89/1.22  #Sup     : 23
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 3
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 4
% 1.89/1.22  #Demod        : 4
% 1.89/1.22  #Tautology    : 1
% 1.89/1.22  #SimpNegUnit  : 4
% 1.89/1.22  #BackRed      : 2
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.89/1.23  Preprocessing        : 0.29
% 1.89/1.23  Parsing              : 0.16
% 1.89/1.23  CNF conversion       : 0.02
% 1.89/1.23  Main loop            : 0.17
% 1.89/1.23  Inferencing          : 0.07
% 1.89/1.23  Reduction            : 0.04
% 1.89/1.23  Demodulation         : 0.03
% 1.89/1.23  BG Simplification    : 0.02
% 1.89/1.23  Subsumption          : 0.02
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.49
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
