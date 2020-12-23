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
% DateTime   : Thu Dec  3 10:31:24 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 130 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_yellow19,type,(
    k1_yellow19: ( $i * $i ) > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r2_waybel_7(A,k1_yellow19(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow19)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k1_yellow19(A,B))
        & v1_subset_1(k1_yellow19(A,B),u1_struct_0(k3_yellow_1(k2_struct_0(A))))
        & v2_waybel_0(k1_yellow19(A,B),k3_yellow_1(k2_struct_0(A)))
        & v13_waybel_0(k1_yellow19(A,B),k3_yellow_1(k2_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow19)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_yellow19(A,B),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow19)).

tff(f_39,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
             => ( r2_waybel_7(A,C,B)
              <=> r1_tarski(k1_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow19)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v13_waybel_0(k1_yellow19(A_10,B_11),k3_yellow_1(k2_struct_0(A_10)))
      | ~ m1_subset_1(B_11,u1_struct_0(A_10))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k1_yellow19(A_8,B_9),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_8)))))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k1_yellow19(A_39,B_40),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_39)))))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden('#skF_1'(A_32,B_33,C_34),B_33)
      | r1_tarski(B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(B_33,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_65,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_yellow19(A_44,B_45),k1_yellow19(A_44,B_45))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_60,c_53])).

tff(c_18,plain,(
    ! [A_12,C_18,B_16] :
      ( r2_waybel_7(A_12,C_18,B_16)
      | ~ r1_tarski(k1_yellow19(A_12,B_16),C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_12)))))
      | ~ v13_waybel_0(C_18,k3_yellow_1(k2_struct_0(A_12)))
      | ~ m1_subset_1(B_16,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_79,plain,(
    ! [A_55,B_56] :
      ( r2_waybel_7(A_55,k1_yellow19(A_55,B_56),B_56)
      | ~ m1_subset_1(k1_yellow19(A_55,B_56),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_55)))))
      | ~ v13_waybel_0(k1_yellow19(A_55,B_56),k3_yellow_1(k2_struct_0(A_55)))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_65,c_18])).

tff(c_83,plain,(
    ! [A_57,B_58] :
      ( r2_waybel_7(A_57,k1_yellow19(A_57,B_58),B_58)
      | ~ v13_waybel_0(k1_yellow19(A_57,B_58),k3_yellow_1(k2_struct_0(A_57)))
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_87,plain,(
    ! [A_59,B_60] :
      ( r2_waybel_7(A_59,k1_yellow19(A_59,B_60),B_60)
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_10,c_83])).

tff(c_22,plain,(
    ~ r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_90,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_22])).

tff(c_93,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_90])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:06:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.21  %$ r2_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.02/1.21  
% 2.02/1.21  %Foreground sorts:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Background operators:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Foreground operators:
% 2.02/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.02/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.02/1.21  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.02/1.21  tff(k1_yellow19, type, k1_yellow19: ($i * $i) > $i).
% 2.02/1.21  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.02/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.02/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.21  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.21  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.02/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.02/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.02/1.21  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.02/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.21  
% 2.02/1.22  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_waybel_7(A, k1_yellow19(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_yellow19)).
% 2.02/1.22  tff(f_68, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (((~v1_xboole_0(k1_yellow19(A, B)) & v1_subset_1(k1_yellow19(A, B), u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(k1_yellow19(A, B), k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(k1_yellow19(A, B), k3_yellow_1(k2_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_yellow19)).
% 2.02/1.22  tff(f_50, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_yellow19(A, B), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow19)).
% 2.02/1.22  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.02/1.22  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((v13_waybel_0(C, k3_yellow_1(k2_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_waybel_7(A, C, B) <=> r1_tarski(k1_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow19)).
% 2.02/1.22  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.02/1.22  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.02/1.22  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.02/1.22  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.02/1.22  tff(c_10, plain, (![A_10, B_11]: (v13_waybel_0(k1_yellow19(A_10, B_11), k3_yellow_1(k2_struct_0(A_10))) | ~m1_subset_1(B_11, u1_struct_0(A_10)) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.22  tff(c_8, plain, (![A_8, B_9]: (m1_subset_1(k1_yellow19(A_8, B_9), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_8))))) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.02/1.22  tff(c_60, plain, (![A_39, B_40]: (m1_subset_1(k1_yellow19(A_39, B_40), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_39))))) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.02/1.22  tff(c_48, plain, (![A_32, B_33, C_34]: (r2_hidden('#skF_1'(A_32, B_33, C_34), B_33) | r1_tarski(B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.22  tff(c_2, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.22  tff(c_53, plain, (![B_33, A_32]: (r1_tarski(B_33, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(resolution, [status(thm)], [c_48, c_2])).
% 2.02/1.22  tff(c_65, plain, (![A_44, B_45]: (r1_tarski(k1_yellow19(A_44, B_45), k1_yellow19(A_44, B_45)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(resolution, [status(thm)], [c_60, c_53])).
% 2.02/1.22  tff(c_18, plain, (![A_12, C_18, B_16]: (r2_waybel_7(A_12, C_18, B_16) | ~r1_tarski(k1_yellow19(A_12, B_16), C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_12))))) | ~v13_waybel_0(C_18, k3_yellow_1(k2_struct_0(A_12))) | ~m1_subset_1(B_16, u1_struct_0(A_12)) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.02/1.22  tff(c_79, plain, (![A_55, B_56]: (r2_waybel_7(A_55, k1_yellow19(A_55, B_56), B_56) | ~m1_subset_1(k1_yellow19(A_55, B_56), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_55))))) | ~v13_waybel_0(k1_yellow19(A_55, B_56), k3_yellow_1(k2_struct_0(A_55))) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_65, c_18])).
% 2.02/1.22  tff(c_83, plain, (![A_57, B_58]: (r2_waybel_7(A_57, k1_yellow19(A_57, B_58), B_58) | ~v13_waybel_0(k1_yellow19(A_57, B_58), k3_yellow_1(k2_struct_0(A_57))) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(resolution, [status(thm)], [c_8, c_79])).
% 2.02/1.22  tff(c_87, plain, (![A_59, B_60]: (r2_waybel_7(A_59, k1_yellow19(A_59, B_60), B_60) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_10, c_83])).
% 2.02/1.22  tff(c_22, plain, (~r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.02/1.22  tff(c_90, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_87, c_22])).
% 2.02/1.22  tff(c_93, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_90])).
% 2.02/1.22  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_93])).
% 2.02/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  Inference rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Ref     : 0
% 2.02/1.22  #Sup     : 11
% 2.02/1.22  #Fact    : 0
% 2.02/1.22  #Define  : 0
% 2.02/1.22  #Split   : 0
% 2.02/1.22  #Chain   : 0
% 2.02/1.22  #Close   : 0
% 2.02/1.22  
% 2.02/1.22  Ordering : KBO
% 2.02/1.22  
% 2.02/1.22  Simplification rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Subsume      : 2
% 2.02/1.22  #Demod        : 5
% 2.02/1.22  #Tautology    : 0
% 2.02/1.22  #SimpNegUnit  : 2
% 2.02/1.22  #BackRed      : 0
% 2.02/1.22  
% 2.02/1.22  #Partial instantiations: 0
% 2.02/1.22  #Strategies tried      : 1
% 2.02/1.22  
% 2.02/1.22  Timing (in seconds)
% 2.02/1.22  ----------------------
% 2.02/1.23  Preprocessing        : 0.29
% 2.02/1.23  Parsing              : 0.17
% 2.02/1.23  CNF conversion       : 0.02
% 2.02/1.23  Main loop            : 0.16
% 2.02/1.23  Inferencing          : 0.07
% 2.02/1.23  Reduction            : 0.04
% 2.02/1.23  Demodulation         : 0.03
% 2.02/1.23  BG Simplification    : 0.01
% 2.02/1.23  Subsumption          : 0.03
% 2.02/1.23  Abstraction          : 0.01
% 2.02/1.23  MUC search           : 0.00
% 2.02/1.23  Cooper               : 0.00
% 2.02/1.23  Total                : 0.47
% 2.02/1.23  Index Insertion      : 0.00
% 2.02/1.23  Index Deletion       : 0.00
% 2.02/1.23  Index Matching       : 0.00
% 2.02/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
