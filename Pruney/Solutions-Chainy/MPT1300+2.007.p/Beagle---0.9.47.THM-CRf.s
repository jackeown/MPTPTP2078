%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:45 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 199 expanded)
%              Number of leaves         :   22 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  151 ( 592 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v1_tops_2(C,A) )
                 => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ~ v1_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_156,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_61)
      | v1_tops_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60))))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_163,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v1_tops_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_156])).

tff(c_170,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v1_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_163])).

tff(c_171,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_170])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_34,C_35,B_36] :
      ( m1_subset_1(A_34,C_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    ! [A_34,B_4,A_3] :
      ( m1_subset_1(A_34,B_4)
      | ~ r2_hidden(A_34,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_182,plain,(
    ! [B_4] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),B_4)
      | ~ r1_tarski('#skF_3',B_4) ) ),
    inference(resolution,[status(thm)],[c_171,c_64])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [C_31,B_32,A_33] :
      ( ~ v1_xboole_0(C_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_31))
      | ~ r2_hidden(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [B_37,A_38,A_39] :
      ( ~ v1_xboole_0(B_37)
      | ~ r2_hidden(A_38,A_39)
      | ~ r1_tarski(A_39,B_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_109,plain,(
    ! [B_53,B_54,A_55] :
      ( ~ v1_xboole_0(B_53)
      | ~ r1_tarski(B_54,B_53)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_124,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_55,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_125,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_22,plain,(
    v1_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_65,plain,(
    ! [A_34] :
      ( m1_subset_1(A_34,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_321,plain,(
    ! [C_77,A_78,B_79] :
      ( v3_pre_topc(C_77,A_78)
      | ~ r2_hidden(C_77,B_79)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v1_tops_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_523,plain,(
    ! [A_105,A_106,B_107] :
      ( v3_pre_topc(A_105,A_106)
      | ~ m1_subset_1(A_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v1_tops_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_106))))
      | ~ l1_pre_topc(A_106)
      | v1_xboole_0(B_107)
      | ~ m1_subset_1(A_105,B_107) ) ),
    inference(resolution,[status(thm)],[c_2,c_321])).

tff(c_532,plain,(
    ! [A_34,B_107] :
      ( v3_pre_topc(A_34,'#skF_2')
      | ~ v1_tops_2(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(B_107)
      | ~ m1_subset_1(A_34,B_107)
      | ~ r2_hidden(A_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_523])).

tff(c_550,plain,(
    ! [A_108,B_109] :
      ( v3_pre_topc(A_108,'#skF_2')
      | ~ v1_tops_2(B_109,'#skF_2')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | v1_xboole_0(B_109)
      | ~ m1_subset_1(A_108,B_109)
      | ~ r2_hidden(A_108,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_532])).

tff(c_558,plain,(
    ! [A_108] :
      ( v3_pre_topc(A_108,'#skF_2')
      | ~ v1_tops_2('#skF_4','#skF_2')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_108,'#skF_4')
      | ~ r2_hidden(A_108,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_550])).

tff(c_566,plain,(
    ! [A_108] :
      ( v3_pre_topc(A_108,'#skF_2')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_108,'#skF_4')
      | ~ r2_hidden(A_108,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_558])).

tff(c_570,plain,(
    ! [A_110] :
      ( v3_pre_topc(A_110,'#skF_2')
      | ~ m1_subset_1(A_110,'#skF_4')
      | ~ r2_hidden(A_110,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_566])).

tff(c_14,plain,(
    ! [A_11,B_17] :
      ( ~ v3_pre_topc('#skF_1'(A_11,B_17),A_11)
      | v1_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_573,plain,(
    ! [B_17] :
      ( v1_tops_2(B_17,'#skF_2')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_2',B_17),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_2',B_17),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_570,c_14])).

tff(c_614,plain,(
    ! [B_113] :
      ( v1_tops_2(B_113,'#skF_2')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_113),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_2',B_113),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_573])).

tff(c_628,plain,
    ( v1_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_614])).

tff(c_635,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_628])).

tff(c_636,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_659,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_636])).

tff(c_662,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_659])).

tff(c_665,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_662])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_665])).

tff(c_670,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_674,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_670])).

tff(c_678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_674])).

tff(c_680,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_705,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),B_123)
      | v1_tops_2(B_123,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_122))))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_712,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v1_tops_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_705])).

tff(c_719,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v1_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_712])).

tff(c_720,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_719])).

tff(c_53,plain,(
    ! [B_4,A_33,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_33,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_736,plain,(
    ! [B_124] :
      ( ~ v1_xboole_0(B_124)
      | ~ r1_tarski('#skF_3',B_124) ) ),
    inference(resolution,[status(thm)],[c_720,c_53])).

tff(c_750,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_736])).

tff(c_757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:55:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.41  
% 2.87/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.41  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.87/1.41  
% 2.87/1.41  %Foreground sorts:
% 2.87/1.41  
% 2.87/1.41  
% 2.87/1.41  %Background operators:
% 2.87/1.41  
% 2.87/1.41  
% 2.87/1.41  %Foreground operators:
% 2.87/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.87/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.41  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.87/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.41  
% 2.87/1.42  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 2.87/1.42  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 2.87/1.42  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.87/1.42  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.87/1.42  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.87/1.42  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.87/1.42  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.42  tff(c_20, plain, (~v1_tops_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.42  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.42  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.42  tff(c_156, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), B_61) | v1_tops_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.42  tff(c_163, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v1_tops_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_156])).
% 2.87/1.42  tff(c_170, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v1_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_163])).
% 2.87/1.42  tff(c_171, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_20, c_170])).
% 2.87/1.42  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.42  tff(c_57, plain, (![A_34, C_35, B_36]: (m1_subset_1(A_34, C_35) | ~m1_subset_1(B_36, k1_zfmisc_1(C_35)) | ~r2_hidden(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.42  tff(c_64, plain, (![A_34, B_4, A_3]: (m1_subset_1(A_34, B_4) | ~r2_hidden(A_34, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_57])).
% 2.87/1.42  tff(c_182, plain, (![B_4]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), B_4) | ~r1_tarski('#skF_3', B_4))), inference(resolution, [status(thm)], [c_171, c_64])).
% 2.87/1.42  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.42  tff(c_46, plain, (![C_31, B_32, A_33]: (~v1_xboole_0(C_31) | ~m1_subset_1(B_32, k1_zfmisc_1(C_31)) | ~r2_hidden(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.87/1.42  tff(c_67, plain, (![B_37, A_38, A_39]: (~v1_xboole_0(B_37) | ~r2_hidden(A_38, A_39) | ~r1_tarski(A_39, B_37))), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.87/1.42  tff(c_109, plain, (![B_53, B_54, A_55]: (~v1_xboole_0(B_53) | ~r1_tarski(B_54, B_53) | v1_xboole_0(B_54) | ~m1_subset_1(A_55, B_54))), inference(resolution, [status(thm)], [c_2, c_67])).
% 2.87/1.42  tff(c_124, plain, (![A_55]: (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_55, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_109])).
% 2.87/1.42  tff(c_125, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_124])).
% 2.87/1.42  tff(c_22, plain, (v1_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.43  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.43  tff(c_65, plain, (![A_34]: (m1_subset_1(A_34, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_34, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_57])).
% 2.87/1.43  tff(c_321, plain, (![C_77, A_78, B_79]: (v3_pre_topc(C_77, A_78) | ~r2_hidden(C_77, B_79) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~v1_tops_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78)))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.43  tff(c_523, plain, (![A_105, A_106, B_107]: (v3_pre_topc(A_105, A_106) | ~m1_subset_1(A_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~v1_tops_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_106)))) | ~l1_pre_topc(A_106) | v1_xboole_0(B_107) | ~m1_subset_1(A_105, B_107))), inference(resolution, [status(thm)], [c_2, c_321])).
% 2.87/1.43  tff(c_532, plain, (![A_34, B_107]: (v3_pre_topc(A_34, '#skF_2') | ~v1_tops_2(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | v1_xboole_0(B_107) | ~m1_subset_1(A_34, B_107) | ~r2_hidden(A_34, '#skF_4'))), inference(resolution, [status(thm)], [c_65, c_523])).
% 2.87/1.43  tff(c_550, plain, (![A_108, B_109]: (v3_pre_topc(A_108, '#skF_2') | ~v1_tops_2(B_109, '#skF_2') | ~m1_subset_1(B_109, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | v1_xboole_0(B_109) | ~m1_subset_1(A_108, B_109) | ~r2_hidden(A_108, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_532])).
% 2.87/1.43  tff(c_558, plain, (![A_108]: (v3_pre_topc(A_108, '#skF_2') | ~v1_tops_2('#skF_4', '#skF_2') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_108, '#skF_4') | ~r2_hidden(A_108, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_550])).
% 2.87/1.43  tff(c_566, plain, (![A_108]: (v3_pre_topc(A_108, '#skF_2') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_108, '#skF_4') | ~r2_hidden(A_108, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_558])).
% 2.87/1.43  tff(c_570, plain, (![A_110]: (v3_pre_topc(A_110, '#skF_2') | ~m1_subset_1(A_110, '#skF_4') | ~r2_hidden(A_110, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_125, c_566])).
% 2.87/1.43  tff(c_14, plain, (![A_11, B_17]: (~v3_pre_topc('#skF_1'(A_11, B_17), A_11) | v1_tops_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.43  tff(c_573, plain, (![B_17]: (v1_tops_2(B_17, '#skF_2') | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_1'('#skF_2', B_17), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', B_17), '#skF_4'))), inference(resolution, [status(thm)], [c_570, c_14])).
% 2.87/1.43  tff(c_614, plain, (![B_113]: (v1_tops_2(B_113, '#skF_2') | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_1'('#skF_2', B_113), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', B_113), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_573])).
% 2.87/1.43  tff(c_628, plain, (v1_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_28, c_614])).
% 2.87/1.43  tff(c_635, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20, c_628])).
% 2.87/1.43  tff(c_636, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_635])).
% 2.87/1.43  tff(c_659, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_2, c_636])).
% 2.87/1.43  tff(c_662, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_125, c_659])).
% 2.87/1.43  tff(c_665, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_182, c_662])).
% 2.87/1.43  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_665])).
% 2.87/1.43  tff(c_670, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_635])).
% 2.87/1.43  tff(c_674, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_182, c_670])).
% 2.87/1.43  tff(c_678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_674])).
% 2.87/1.43  tff(c_680, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_124])).
% 2.87/1.43  tff(c_705, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), B_123) | v1_tops_2(B_123, A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_122)))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.43  tff(c_712, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v1_tops_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_705])).
% 2.87/1.43  tff(c_719, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v1_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_712])).
% 2.87/1.43  tff(c_720, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_20, c_719])).
% 2.87/1.43  tff(c_53, plain, (![B_4, A_33, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_33, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.87/1.43  tff(c_736, plain, (![B_124]: (~v1_xboole_0(B_124) | ~r1_tarski('#skF_3', B_124))), inference(resolution, [status(thm)], [c_720, c_53])).
% 2.87/1.43  tff(c_750, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_736])).
% 2.87/1.43  tff(c_757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_680, c_750])).
% 2.87/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.43  
% 2.87/1.43  Inference rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Ref     : 0
% 2.87/1.43  #Sup     : 159
% 2.87/1.43  #Fact    : 0
% 2.87/1.43  #Define  : 0
% 2.87/1.43  #Split   : 17
% 2.87/1.43  #Chain   : 0
% 2.87/1.43  #Close   : 0
% 2.87/1.43  
% 2.87/1.43  Ordering : KBO
% 2.87/1.43  
% 2.87/1.43  Simplification rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Subsume      : 45
% 2.87/1.43  #Demod        : 51
% 2.87/1.43  #Tautology    : 20
% 2.87/1.43  #SimpNegUnit  : 24
% 2.87/1.43  #BackRed      : 0
% 2.87/1.43  
% 2.87/1.43  #Partial instantiations: 0
% 2.87/1.43  #Strategies tried      : 1
% 2.87/1.43  
% 2.87/1.43  Timing (in seconds)
% 2.87/1.43  ----------------------
% 2.87/1.43  Preprocessing        : 0.28
% 2.87/1.43  Parsing              : 0.16
% 2.87/1.43  CNF conversion       : 0.02
% 2.87/1.43  Main loop            : 0.40
% 2.87/1.43  Inferencing          : 0.15
% 2.87/1.43  Reduction            : 0.11
% 2.87/1.43  Demodulation         : 0.07
% 2.87/1.43  BG Simplification    : 0.02
% 2.87/1.43  Subsumption          : 0.09
% 2.87/1.43  Abstraction          : 0.02
% 2.87/1.43  MUC search           : 0.00
% 2.87/1.43  Cooper               : 0.00
% 2.87/1.43  Total                : 0.71
% 2.87/1.43  Index Insertion      : 0.00
% 2.87/1.43  Index Deletion       : 0.00
% 2.87/1.43  Index Matching       : 0.00
% 2.87/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
