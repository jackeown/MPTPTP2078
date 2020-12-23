%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:47 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   41 (  60 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 205 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k6_domain_1 > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ r2_hidden(B,k3_orders_2(A,C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> r2_hidden(C,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_24,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_22,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14,plain,(
    r2_hidden('#skF_2',k3_orders_2('#skF_1','#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_49,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( r2_orders_2(A_44,B_45,C_46)
      | ~ r2_hidden(B_45,k3_orders_2(A_44,D_47,C_46))
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(C_46,u1_struct_0(A_44))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44)
      | ~ v4_orders_2(A_44)
      | ~ v3_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_51,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_49])).

tff(c_54,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_18,c_16,c_51])).

tff(c_55,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_54])).

tff(c_30,plain,(
    ! [C_32,A_33,B_34] :
      ( r2_hidden(C_32,k1_orders_2(A_33,k6_domain_1(u1_struct_0(A_33),B_34)))
      | ~ r2_orders_2(A_33,B_34,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_33))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v3_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( ~ r2_hidden(B_3,k1_orders_2(A_1,k6_domain_1(u1_struct_0(A_1),B_3)))
      | ~ m1_subset_1(B_3,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,(
    ! [A_33,B_34] :
      ( ~ r2_orders_2(A_33,B_34,B_34)
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v3_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_30,c_2])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_55,c_35])).

tff(c_67,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_18,c_64])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.37  % Computer   : n022.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 13:28:40 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.38  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.18  
% 1.96/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.18  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k6_domain_1 > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.18  
% 1.99/1.18  %Foreground sorts:
% 1.99/1.18  
% 1.99/1.18  
% 1.99/1.18  %Background operators:
% 1.99/1.18  
% 1.99/1.18  
% 1.99/1.18  %Foreground operators:
% 1.99/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.99/1.18  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.99/1.18  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.18  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 1.99/1.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.99/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.18  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.99/1.18  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.99/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.18  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 1.99/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.18  
% 1.99/1.20  tff(f_110, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~r2_hidden(B, k3_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_orders_2)).
% 1.99/1.20  tff(f_89, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 1.99/1.20  tff(f_63, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(C, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_orders_2)).
% 1.99/1.20  tff(f_42, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 1.99/1.20  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 1.99/1.20  tff(c_26, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 1.99/1.20  tff(c_24, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 1.99/1.20  tff(c_22, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 1.99/1.20  tff(c_20, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 1.99/1.20  tff(c_18, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 1.99/1.20  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 1.99/1.20  tff(c_14, plain, (r2_hidden('#skF_2', k3_orders_2('#skF_1', '#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 1.99/1.20  tff(c_49, plain, (![A_44, B_45, C_46, D_47]: (r2_orders_2(A_44, B_45, C_46) | ~r2_hidden(B_45, k3_orders_2(A_44, D_47, C_46)) | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(C_46, u1_struct_0(A_44)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_orders_2(A_44) | ~v5_orders_2(A_44) | ~v4_orders_2(A_44) | ~v3_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.99/1.20  tff(c_51, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_49])).
% 1.99/1.20  tff(c_54, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_18, c_16, c_51])).
% 1.99/1.20  tff(c_55, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_54])).
% 1.99/1.20  tff(c_30, plain, (![C_32, A_33, B_34]: (r2_hidden(C_32, k1_orders_2(A_33, k6_domain_1(u1_struct_0(A_33), B_34))) | ~r2_orders_2(A_33, B_34, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_33)) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33) | ~v4_orders_2(A_33) | ~v3_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.20  tff(c_2, plain, (![B_3, A_1]: (~r2_hidden(B_3, k1_orders_2(A_1, k6_domain_1(u1_struct_0(A_1), B_3))) | ~m1_subset_1(B_3, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.20  tff(c_35, plain, (![A_33, B_34]: (~r2_orders_2(A_33, B_34, B_34) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33) | ~v4_orders_2(A_33) | ~v3_orders_2(A_33) | v2_struct_0(A_33))), inference(resolution, [status(thm)], [c_30, c_2])).
% 1.99/1.20  tff(c_64, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_55, c_35])).
% 1.99/1.20  tff(c_67, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_18, c_64])).
% 1.99/1.20  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_67])).
% 1.99/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  Inference rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Ref     : 0
% 1.99/1.20  #Sup     : 6
% 1.99/1.20  #Fact    : 0
% 1.99/1.20  #Define  : 0
% 1.99/1.20  #Split   : 0
% 1.99/1.20  #Chain   : 0
% 1.99/1.20  #Close   : 0
% 1.99/1.20  
% 1.99/1.20  Ordering : KBO
% 1.99/1.20  
% 1.99/1.20  Simplification rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Subsume      : 0
% 1.99/1.20  #Demod        : 21
% 1.99/1.20  #Tautology    : 1
% 1.99/1.20  #SimpNegUnit  : 4
% 1.99/1.20  #BackRed      : 0
% 1.99/1.20  
% 1.99/1.20  #Partial instantiations: 0
% 1.99/1.20  #Strategies tried      : 1
% 1.99/1.20  
% 1.99/1.20  Timing (in seconds)
% 1.99/1.20  ----------------------
% 1.99/1.20  Preprocessing        : 0.28
% 1.99/1.20  Parsing              : 0.16
% 1.99/1.20  CNF conversion       : 0.02
% 1.99/1.20  Main loop            : 0.13
% 1.99/1.20  Inferencing          : 0.06
% 1.99/1.20  Reduction            : 0.04
% 1.99/1.20  Demodulation         : 0.03
% 1.99/1.20  BG Simplification    : 0.01
% 1.99/1.20  Subsumption          : 0.02
% 1.99/1.20  Abstraction          : 0.01
% 1.99/1.20  MUC search           : 0.00
% 1.99/1.20  Cooper               : 0.00
% 1.99/1.20  Total                : 0.44
% 1.99/1.20  Index Insertion      : 0.00
% 1.99/1.20  Index Deletion       : 0.00
% 1.99/1.20  Index Matching       : 0.00
% 1.99/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
