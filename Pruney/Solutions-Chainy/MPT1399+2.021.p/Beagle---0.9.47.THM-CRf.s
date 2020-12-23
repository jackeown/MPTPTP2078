%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:21 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 251 expanded)
%              Number of leaves         :   34 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 709 expanded)
%              Number of equality atoms :    8 (  81 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_38,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    ! [A_18] :
      ( v4_pre_topc(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_68,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_73,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_77,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_98,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(u1_struct_0(A_45))
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_98])).

tff(c_102,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_101])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_108,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_108])).

tff(c_113,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_79,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_42])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_19] :
      ( v3_pre_topc(k2_struct_0(A_19),A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [C_41,A_42] :
      ( r2_hidden(C_41,k1_zfmisc_1(A_42))
      | ~ r1_tarski(C_41,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_91,plain,(
    ! [C_41,A_42] :
      ( m1_subset_1(C_41,k1_zfmisc_1(A_42))
      | ~ r1_tarski(C_41,A_42) ) ),
    inference(resolution,[status(thm)],[c_84,c_22])).

tff(c_54,plain,(
    ! [D_31] :
      ( v4_pre_topc(D_31,'#skF_3')
      | ~ r2_hidden(D_31,'#skF_5')
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_195,plain,(
    ! [D_63] :
      ( v4_pre_topc(D_63,'#skF_3')
      | ~ r2_hidden(D_63,'#skF_5')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_54])).

tff(c_428,plain,(
    ! [C_83] :
      ( v4_pre_topc(C_83,'#skF_3')
      | ~ r2_hidden(C_83,'#skF_5')
      | ~ r1_tarski(C_83,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_91,c_195])).

tff(c_437,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_428])).

tff(c_452,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_50,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,'#skF_5')
      | ~ r2_hidden('#skF_4',D_31)
      | ~ v4_pre_topc(D_31,'#skF_3')
      | ~ v3_pre_topc(D_31,'#skF_3')
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_446,plain,(
    ! [D_84] :
      ( r2_hidden(D_84,'#skF_5')
      | ~ r2_hidden('#skF_4',D_84)
      | ~ v4_pre_topc(D_84,'#skF_3')
      | ~ v3_pre_topc(D_84,'#skF_3')
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_50])).

tff(c_566,plain,(
    ! [C_96] :
      ( r2_hidden(C_96,'#skF_5')
      | ~ r2_hidden('#skF_4',C_96)
      | ~ v4_pre_topc(C_96,'#skF_3')
      | ~ v3_pre_topc(C_96,'#skF_3')
      | ~ r1_tarski(C_96,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_91,c_446])).

tff(c_578,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_566])).

tff(c_587,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_578])).

tff(c_676,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_587])).

tff(c_679,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_676])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_679])).

tff(c_684,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_587])).

tff(c_686,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_704,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_686])).

tff(c_707,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_704])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_707])).

tff(c_710,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_723,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_710])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_723])).

tff(c_729,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_746,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_729,c_26])).

tff(c_751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:15:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.41  
% 2.75/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.41  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.75/1.41  
% 2.75/1.41  %Foreground sorts:
% 2.75/1.41  
% 2.75/1.41  
% 2.75/1.41  %Background operators:
% 2.75/1.41  
% 2.75/1.41  
% 2.75/1.41  %Foreground operators:
% 2.75/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.75/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.75/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.75/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.75/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.41  
% 2.75/1.43  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.75/1.43  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.75/1.43  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.75/1.43  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.75/1.43  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.75/1.43  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.75/1.43  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.75/1.43  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.75/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.75/1.43  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.75/1.43  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.75/1.43  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.75/1.43  tff(c_38, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.43  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.43  tff(c_57, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8])).
% 2.75/1.43  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.43  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.43  tff(c_34, plain, (![A_18]: (v4_pre_topc(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.43  tff(c_30, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.43  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.43  tff(c_68, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.75/1.43  tff(c_73, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_30, c_68])).
% 2.75/1.43  tff(c_77, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_73])).
% 2.75/1.43  tff(c_98, plain, (![A_45]: (~v1_xboole_0(u1_struct_0(A_45)) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.75/1.43  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77, c_98])).
% 2.75/1.43  tff(c_102, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_101])).
% 2.75/1.43  tff(c_105, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_102])).
% 2.75/1.43  tff(c_108, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_105])).
% 2.75/1.43  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_108])).
% 2.75/1.43  tff(c_113, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_102])).
% 2.75/1.43  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.43  tff(c_79, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_42])).
% 2.75/1.43  tff(c_24, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.75/1.43  tff(c_36, plain, (![A_19]: (v3_pre_topc(k2_struct_0(A_19), A_19) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.43  tff(c_84, plain, (![C_41, A_42]: (r2_hidden(C_41, k1_zfmisc_1(A_42)) | ~r1_tarski(C_41, A_42))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.43  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.75/1.43  tff(c_91, plain, (![C_41, A_42]: (m1_subset_1(C_41, k1_zfmisc_1(A_42)) | ~r1_tarski(C_41, A_42))), inference(resolution, [status(thm)], [c_84, c_22])).
% 2.75/1.43  tff(c_54, plain, (![D_31]: (v4_pre_topc(D_31, '#skF_3') | ~r2_hidden(D_31, '#skF_5') | ~m1_subset_1(D_31, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.43  tff(c_195, plain, (![D_63]: (v4_pre_topc(D_63, '#skF_3') | ~r2_hidden(D_63, '#skF_5') | ~m1_subset_1(D_63, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_54])).
% 2.75/1.43  tff(c_428, plain, (![C_83]: (v4_pre_topc(C_83, '#skF_3') | ~r2_hidden(C_83, '#skF_5') | ~r1_tarski(C_83, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_91, c_195])).
% 2.75/1.43  tff(c_437, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_428])).
% 2.75/1.43  tff(c_452, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_437])).
% 2.75/1.43  tff(c_50, plain, (![D_31]: (r2_hidden(D_31, '#skF_5') | ~r2_hidden('#skF_4', D_31) | ~v4_pre_topc(D_31, '#skF_3') | ~v3_pre_topc(D_31, '#skF_3') | ~m1_subset_1(D_31, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.43  tff(c_446, plain, (![D_84]: (r2_hidden(D_84, '#skF_5') | ~r2_hidden('#skF_4', D_84) | ~v4_pre_topc(D_84, '#skF_3') | ~v3_pre_topc(D_84, '#skF_3') | ~m1_subset_1(D_84, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_50])).
% 2.75/1.43  tff(c_566, plain, (![C_96]: (r2_hidden(C_96, '#skF_5') | ~r2_hidden('#skF_4', C_96) | ~v4_pre_topc(C_96, '#skF_3') | ~v3_pre_topc(C_96, '#skF_3') | ~r1_tarski(C_96, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_91, c_446])).
% 2.75/1.43  tff(c_578, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_566])).
% 2.75/1.43  tff(c_587, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_452, c_578])).
% 2.75/1.43  tff(c_676, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_587])).
% 2.75/1.43  tff(c_679, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_676])).
% 2.75/1.43  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_679])).
% 2.75/1.43  tff(c_684, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_587])).
% 2.75/1.43  tff(c_686, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_684])).
% 2.75/1.43  tff(c_704, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_686])).
% 2.75/1.43  tff(c_707, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_704])).
% 2.75/1.43  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_707])).
% 2.75/1.43  tff(c_710, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_684])).
% 2.75/1.43  tff(c_723, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_710])).
% 2.75/1.43  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_723])).
% 2.75/1.43  tff(c_729, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_437])).
% 2.75/1.43  tff(c_26, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.43  tff(c_746, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_729, c_26])).
% 2.75/1.43  tff(c_751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_746])).
% 2.75/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  
% 2.75/1.43  Inference rules
% 2.75/1.43  ----------------------
% 2.75/1.43  #Ref     : 0
% 2.75/1.43  #Sup     : 129
% 2.75/1.43  #Fact    : 0
% 2.75/1.43  #Define  : 0
% 2.75/1.43  #Split   : 14
% 2.75/1.43  #Chain   : 0
% 2.75/1.43  #Close   : 0
% 2.75/1.43  
% 2.75/1.43  Ordering : KBO
% 2.75/1.43  
% 2.75/1.43  Simplification rules
% 2.75/1.43  ----------------------
% 2.75/1.43  #Subsume      : 15
% 2.75/1.43  #Demod        : 40
% 2.75/1.43  #Tautology    : 28
% 2.75/1.43  #SimpNegUnit  : 15
% 2.75/1.43  #BackRed      : 2
% 2.75/1.43  
% 2.75/1.43  #Partial instantiations: 0
% 2.75/1.43  #Strategies tried      : 1
% 2.75/1.43  
% 2.75/1.43  Timing (in seconds)
% 2.75/1.43  ----------------------
% 2.75/1.43  Preprocessing        : 0.32
% 2.75/1.43  Parsing              : 0.17
% 2.75/1.43  CNF conversion       : 0.02
% 2.75/1.43  Main loop            : 0.34
% 2.75/1.43  Inferencing          : 0.12
% 2.75/1.43  Reduction            : 0.10
% 2.75/1.43  Demodulation         : 0.06
% 2.75/1.43  BG Simplification    : 0.02
% 2.75/1.43  Subsumption          : 0.07
% 2.75/1.43  Abstraction          : 0.02
% 2.75/1.43  MUC search           : 0.00
% 2.75/1.43  Cooper               : 0.00
% 2.75/1.43  Total                : 0.70
% 2.75/1.43  Index Insertion      : 0.00
% 2.75/1.43  Index Deletion       : 0.00
% 2.75/1.43  Index Matching       : 0.00
% 2.75/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
