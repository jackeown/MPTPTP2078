%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1301+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:45 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 190 expanded)
%              Number of leaves         :   22 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  128 ( 575 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v2_tops_2(C,A) )
                 => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ~ v2_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_100,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),B_48)
      | v2_tops_2(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47))))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_114,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_107])).

tff(c_115,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_114])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_57,plain,(
    ! [A_34,C_35,B_36] :
      ( m1_subset_1(A_34,C_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    ! [A_34,B_14,A_13] :
      ( m1_subset_1(A_34,B_14)
      | ~ r2_hidden(A_34,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_57])).

tff(c_120,plain,(
    ! [B_14] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),B_14)
      | ~ r1_tarski('#skF_3',B_14) ) ),
    inference(resolution,[status(thm)],[c_115,c_64])).

tff(c_46,plain,(
    ! [C_31,B_32,A_33] :
      ( ~ v1_xboole_0(C_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_31))
      | ~ r2_hidden(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53,plain,(
    ! [B_14,A_33,A_13] :
      ( ~ v1_xboole_0(B_14)
      | ~ r2_hidden(A_33,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_46])).

tff(c_122,plain,(
    ! [B_49] :
      ( ~ v1_xboole_0(B_49)
      | ~ r1_tarski('#skF_3',B_49) ) ),
    inference(resolution,[status(thm)],[c_115,c_53])).

tff(c_140,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_122])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_65,plain,(
    ! [A_34] :
      ( m1_subset_1(A_34,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_345,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_pre_topc(C_77,A_78)
      | ~ r2_hidden(C_77,B_79)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v2_tops_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_508,plain,(
    ! [A_100,A_101,B_102] :
      ( v4_pre_topc(A_100,A_101)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v2_tops_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101))))
      | ~ l1_pre_topc(A_101)
      | v1_xboole_0(B_102)
      | ~ m1_subset_1(A_100,B_102) ) ),
    inference(resolution,[status(thm)],[c_10,c_345])).

tff(c_517,plain,(
    ! [A_34,B_102] :
      ( v4_pre_topc(A_34,'#skF_2')
      | ~ v2_tops_2(B_102,'#skF_2')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(B_102)
      | ~ m1_subset_1(A_34,B_102)
      | ~ r2_hidden(A_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_508])).

tff(c_535,plain,(
    ! [A_103,B_104] :
      ( v4_pre_topc(A_103,'#skF_2')
      | ~ v2_tops_2(B_104,'#skF_2')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | v1_xboole_0(B_104)
      | ~ m1_subset_1(A_103,B_104)
      | ~ r2_hidden(A_103,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_517])).

tff(c_543,plain,(
    ! [A_103] :
      ( v4_pre_topc(A_103,'#skF_2')
      | ~ v2_tops_2('#skF_4','#skF_2')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_103,'#skF_4')
      | ~ r2_hidden(A_103,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_535])).

tff(c_551,plain,(
    ! [A_103] :
      ( v4_pre_topc(A_103,'#skF_2')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_103,'#skF_4')
      | ~ r2_hidden(A_103,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_543])).

tff(c_555,plain,(
    ! [A_105] :
      ( v4_pre_topc(A_105,'#skF_2')
      | ~ m1_subset_1(A_105,'#skF_4')
      | ~ r2_hidden(A_105,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_551])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v4_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v2_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_558,plain,(
    ! [B_7] :
      ( v2_tops_2(B_7,'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_2',B_7),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_2',B_7),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_555,c_4])).

tff(c_599,plain,(
    ! [B_108] :
      ( v2_tops_2(B_108,'#skF_2')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_108),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_2',B_108),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_558])).

tff(c_613,plain,
    ( v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_599])).

tff(c_620,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_613])).

tff(c_621,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_620])).

tff(c_644,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_621])).

tff(c_647,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_644])).

tff(c_650,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_647])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_650])).

tff(c_655,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_620])).

tff(c_659,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_655])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_659])).

%------------------------------------------------------------------------------
