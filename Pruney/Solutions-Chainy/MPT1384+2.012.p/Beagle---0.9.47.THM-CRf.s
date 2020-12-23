%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:15 EST 2020

% Result     : Theorem 20.86s
% Output     : CNFRefutation 21.09s
% Verified   : 
% Statistics : Number of formulae       :  237 (1094 expanded)
%              Number of leaves         :   32 ( 380 expanded)
%              Depth                    :   34
%              Number of atoms          :  752 (4328 expanded)
%              Number of equality atoms :   19 (  81 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_183,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( m1_connsp_2(D,A,C)
                              & r1_tarski(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_52,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_156,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_87,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_88,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | ~ m1_subset_1(A_94,k1_zfmisc_1(B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_88])).

tff(c_151,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(k1_tops_1(A_113,B_114),B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_157,plain,(
    ! [A_113,A_14] :
      ( r1_tarski(k1_tops_1(A_113,A_14),A_14)
      | ~ l1_pre_topc(A_113)
      | ~ r1_tarski(A_14,u1_struct_0(A_113)) ) ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_24,plain,(
    ! [A_22,B_26,C_28] :
      ( r1_tarski(k1_tops_1(A_22,B_26),k1_tops_1(A_22,C_28))
      | ~ r1_tarski(B_26,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_156,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_151])).

tff(c_160,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_156])).

tff(c_292,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_hidden('#skF_1'(A_139,B_140,C_141),B_140)
      | r1_tarski(B_140,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(A_139))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_500,plain,(
    ! [A_184,B_185,C_186,A_187] :
      ( r2_hidden('#skF_1'(A_184,B_185,C_186),A_187)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_187))
      | r1_tarski(B_185,C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(A_184))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_184)) ) ),
    inference(resolution,[status(thm)],[c_292,c_8])).

tff(c_15620,plain,(
    ! [A_1371,B_1373,A_1372,A_1370,C_1369] :
      ( r2_hidden('#skF_1'(A_1372,B_1373,C_1369),A_1371)
      | ~ m1_subset_1(A_1370,k1_zfmisc_1(A_1371))
      | ~ m1_subset_1(B_1373,k1_zfmisc_1(A_1370))
      | r1_tarski(B_1373,C_1369)
      | ~ m1_subset_1(C_1369,k1_zfmisc_1(A_1372))
      | ~ m1_subset_1(B_1373,k1_zfmisc_1(A_1372)) ) ),
    inference(resolution,[status(thm)],[c_500,c_8])).

tff(c_18722,plain,(
    ! [A_1527,A_1529,B_1528,B_1525,C_1526] :
      ( r2_hidden('#skF_1'(A_1527,B_1525,C_1526),B_1528)
      | ~ m1_subset_1(B_1525,k1_zfmisc_1(A_1529))
      | r1_tarski(B_1525,C_1526)
      | ~ m1_subset_1(C_1526,k1_zfmisc_1(A_1527))
      | ~ m1_subset_1(B_1525,k1_zfmisc_1(A_1527))
      | ~ r1_tarski(A_1529,B_1528) ) ),
    inference(resolution,[status(thm)],[c_18,c_15620])).

tff(c_19422,plain,(
    ! [B_1555,C_1559,A_1558,B_1557,A_1556] :
      ( r2_hidden('#skF_1'(A_1556,A_1558,C_1559),B_1555)
      | r1_tarski(A_1558,C_1559)
      | ~ m1_subset_1(C_1559,k1_zfmisc_1(A_1556))
      | ~ m1_subset_1(A_1558,k1_zfmisc_1(A_1556))
      | ~ r1_tarski(B_1557,B_1555)
      | ~ r1_tarski(A_1558,B_1557) ) ),
    inference(resolution,[status(thm)],[c_18,c_18722])).

tff(c_19851,plain,(
    ! [A_1579,A_1580,C_1581] :
      ( r2_hidden('#skF_1'(A_1579,A_1580,C_1581),'#skF_4')
      | r1_tarski(A_1580,C_1581)
      | ~ m1_subset_1(C_1581,k1_zfmisc_1(A_1579))
      | ~ m1_subset_1(A_1580,k1_zfmisc_1(A_1579))
      | ~ r1_tarski(A_1580,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_160,c_19422])).

tff(c_10,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19866,plain,(
    ! [A_1582,A_1583] :
      ( r1_tarski(A_1582,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1583))
      | ~ m1_subset_1(A_1582,k1_zfmisc_1(A_1583))
      | ~ r1_tarski(A_1582,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_19851,c_10])).

tff(c_19978,plain,(
    ! [A_1588,B_1589] :
      ( r1_tarski(A_1588,'#skF_4')
      | ~ m1_subset_1(A_1588,k1_zfmisc_1(B_1589))
      | ~ r1_tarski(A_1588,k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_1589) ) ),
    inference(resolution,[status(thm)],[c_18,c_19866])).

tff(c_20023,plain,(
    ! [A_1590,B_1591] :
      ( r1_tarski(A_1590,'#skF_4')
      | ~ r1_tarski(A_1590,k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_1591)
      | ~ r1_tarski(A_1590,B_1591) ) ),
    inference(resolution,[status(thm)],[c_18,c_19978])).

tff(c_20035,plain,(
    ! [B_26,B_1591] :
      ( r1_tarski(k1_tops_1('#skF_3',B_26),'#skF_4')
      | ~ r1_tarski('#skF_4',B_1591)
      | ~ r1_tarski(k1_tops_1('#skF_3',B_26),B_1591)
      | ~ r1_tarski(B_26,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_20023])).

tff(c_20174,plain,(
    ! [B_1595,B_1596] :
      ( r1_tarski(k1_tops_1('#skF_3',B_1595),'#skF_4')
      | ~ r1_tarski('#skF_4',B_1596)
      | ~ r1_tarski(k1_tops_1('#skF_3',B_1595),B_1596)
      | ~ r1_tarski(B_1595,'#skF_4')
      | ~ m1_subset_1(B_1595,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_20035])).

tff(c_20202,plain,(
    ! [A_14] :
      ( r1_tarski(k1_tops_1('#skF_3',A_14),'#skF_4')
      | ~ r1_tarski('#skF_4',A_14)
      | ~ r1_tarski(A_14,'#skF_4')
      | ~ m1_subset_1(A_14,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_14,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_157,c_20174])).

tff(c_20473,plain,(
    ! [A_1602] :
      ( r1_tarski(k1_tops_1('#skF_3',A_1602),'#skF_4')
      | ~ r1_tarski('#skF_4',A_1602)
      | ~ r1_tarski(A_1602,'#skF_4')
      | ~ m1_subset_1(A_1602,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_1602,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20202])).

tff(c_20525,plain,(
    ! [A_14] :
      ( r1_tarski(k1_tops_1('#skF_3',A_14),'#skF_4')
      | ~ r1_tarski('#skF_4',A_14)
      | ~ r1_tarski(A_14,'#skF_4')
      | ~ r1_tarski(A_14,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_20473])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_198,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_19494,plain,(
    ! [A_1556,A_1558,C_1559,B_2] :
      ( r2_hidden('#skF_1'(A_1556,A_1558,C_1559),B_2)
      | r1_tarski(A_1558,C_1559)
      | ~ m1_subset_1(C_1559,k1_zfmisc_1(A_1556))
      | ~ m1_subset_1(A_1558,k1_zfmisc_1(A_1556))
      | ~ r1_tarski(A_1558,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_19422])).

tff(c_110,plain,(
    ! [A_100,C_101,B_102] :
      ( m1_subset_1(A_100,C_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(C_101))
      | ~ r2_hidden(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116,plain,(
    ! [A_100] :
      ( m1_subset_1(A_100,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_100,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_110])).

tff(c_68,plain,(
    ! [C_91] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | r1_tarski('#skF_6'(C_91),'#skF_4')
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_122,plain,(
    ! [C_91] :
      ( r1_tarski('#skF_6'(C_91),'#skF_4')
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_68])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_84,plain,(
    ! [C_91] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | m1_subset_1('#skF_6'(C_91),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_248,plain,(
    ! [C_91] :
      ( m1_subset_1('#skF_6'(C_91),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_84])).

tff(c_76,plain,(
    ! [C_91] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | m1_connsp_2('#skF_6'(C_91),'#skF_3',C_91)
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_235,plain,(
    ! [C_91] :
      ( m1_connsp_2('#skF_6'(C_91),'#skF_3',C_91)
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_76])).

tff(c_809,plain,(
    ! [B_220,A_221,C_222] :
      ( r2_hidden(B_220,k1_tops_1(A_221,C_222))
      | ~ m1_connsp_2(C_222,A_221,B_220)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ m1_subset_1(B_220,u1_struct_0(A_221))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_819,plain,(
    ! [B_220,C_91] :
      ( r2_hidden(B_220,k1_tops_1('#skF_3','#skF_6'(C_91)))
      | ~ m1_connsp_2('#skF_6'(C_91),'#skF_3',B_220)
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_248,c_809])).

tff(c_830,plain,(
    ! [B_220,C_91] :
      ( r2_hidden(B_220,k1_tops_1('#skF_3','#skF_6'(C_91)))
      | ~ m1_connsp_2('#skF_6'(C_91),'#skF_3',B_220)
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_819])).

tff(c_881,plain,(
    ! [B_226,C_227] :
      ( r2_hidden(B_226,k1_tops_1('#skF_3','#skF_6'(C_227)))
      | ~ m1_connsp_2('#skF_6'(C_227),'#skF_3',B_226)
      | ~ m1_subset_1(B_226,u1_struct_0('#skF_3'))
      | ~ r2_hidden(C_227,'#skF_4')
      | ~ m1_subset_1(C_227,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_830])).

tff(c_16381,plain,(
    ! [B_1400,A_1401,C_1402] :
      ( r2_hidden(B_1400,A_1401)
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_6'(C_1402)),k1_zfmisc_1(A_1401))
      | ~ m1_connsp_2('#skF_6'(C_1402),'#skF_3',B_1400)
      | ~ m1_subset_1(B_1400,u1_struct_0('#skF_3'))
      | ~ r2_hidden(C_1402,'#skF_4')
      | ~ m1_subset_1(C_1402,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_881,c_8])).

tff(c_24187,plain,(
    ! [B_1742,B_1743,C_1744] :
      ( r2_hidden(B_1742,B_1743)
      | ~ m1_connsp_2('#skF_6'(C_1744),'#skF_3',B_1742)
      | ~ m1_subset_1(B_1742,u1_struct_0('#skF_3'))
      | ~ r2_hidden(C_1744,'#skF_4')
      | ~ m1_subset_1(C_1744,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_6'(C_1744)),B_1743) ) ),
    inference(resolution,[status(thm)],[c_18,c_16381])).

tff(c_24230,plain,(
    ! [C_1745,B_1746] :
      ( r2_hidden(C_1745,B_1746)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_6'(C_1745)),B_1746)
      | ~ r2_hidden(C_1745,'#skF_4')
      | ~ m1_subset_1(C_1745,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_235,c_24187])).

tff(c_24257,plain,(
    ! [C_1745,C_28] :
      ( r2_hidden(C_1745,k1_tops_1('#skF_3',C_28))
      | ~ r2_hidden(C_1745,'#skF_4')
      | ~ m1_subset_1(C_1745,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'(C_1745),C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_6'(C_1745),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_24230])).

tff(c_39809,plain,(
    ! [C_2414,C_2415] :
      ( r2_hidden(C_2414,k1_tops_1('#skF_3',C_2415))
      | ~ r2_hidden(C_2414,'#skF_4')
      | ~ m1_subset_1(C_2414,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'(C_2414),C_2415)
      | ~ m1_subset_1(C_2415,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_6'(C_2414),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24257])).

tff(c_39857,plain,(
    ! [C_2416] :
      ( r2_hidden(C_2416,k1_tops_1('#skF_3','#skF_4'))
      | ~ r2_hidden(C_2416,'#skF_4')
      | ~ m1_subset_1(C_2416,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'(C_2416),'#skF_4')
      | ~ m1_subset_1('#skF_6'(C_2416),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_39809])).

tff(c_39866,plain,(
    ! [C_2417] :
      ( r2_hidden(C_2417,k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_6'(C_2417),'#skF_4')
      | ~ r2_hidden(C_2417,'#skF_4')
      | ~ m1_subset_1(C_2417,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_248,c_39857])).

tff(c_40,plain,(
    ! [C_62,A_56,B_60] :
      ( m1_connsp_2(C_62,A_56,B_60)
      | ~ r2_hidden(B_60,k1_tops_1(A_56,C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_60,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_39883,plain,(
    ! [C_2417] :
      ( m1_connsp_2('#skF_4','#skF_3',C_2417)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_6'(C_2417),'#skF_4')
      | ~ r2_hidden(C_2417,'#skF_4')
      | ~ m1_subset_1(C_2417,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_39866,c_40])).

tff(c_39912,plain,(
    ! [C_2417] :
      ( m1_connsp_2('#skF_4','#skF_3',C_2417)
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_6'(C_2417),'#skF_4')
      | ~ r2_hidden(C_2417,'#skF_4')
      | ~ m1_subset_1(C_2417,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_39883])).

tff(c_39923,plain,(
    ! [C_2418] :
      ( m1_connsp_2('#skF_4','#skF_3',C_2418)
      | ~ r1_tarski('#skF_6'(C_2418),'#skF_4')
      | ~ r2_hidden(C_2418,'#skF_4')
      | ~ m1_subset_1(C_2418,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_39912])).

tff(c_39928,plain,(
    ! [C_2419] :
      ( m1_connsp_2('#skF_4','#skF_3',C_2419)
      | ~ r2_hidden(C_2419,'#skF_4')
      | ~ m1_subset_1(C_2419,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_122,c_39923])).

tff(c_40005,plain,(
    ! [A_2420] :
      ( m1_connsp_2('#skF_4','#skF_3',A_2420)
      | ~ r2_hidden(A_2420,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_116,c_39928])).

tff(c_18753,plain,(
    ! [A_1530,C_1531,B_1532] :
      ( r2_hidden('#skF_1'(A_1530,'#skF_4',C_1531),B_1532)
      | r1_tarski('#skF_4',C_1531)
      | ~ m1_subset_1(C_1531,k1_zfmisc_1(A_1530))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1530))
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_1532) ) ),
    inference(resolution,[status(thm)],[c_46,c_18722])).

tff(c_64,plain,(
    ! [C_91] :
      ( r2_hidden('#skF_5','#skF_4')
      | r1_tarski('#skF_6'(C_91),'#skF_4')
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_93,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_118,plain,(
    ! [A_104,B_105,A_106] :
      ( m1_subset_1(A_104,B_105)
      | ~ r2_hidden(A_104,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(resolution,[status(thm)],[c_18,c_110])).

tff(c_127,plain,(
    ! [B_108] :
      ( m1_subset_1('#skF_5',B_108)
      | ~ r1_tarski('#skF_4',B_108) ) ),
    inference(resolution,[status(thm)],[c_93,c_118])).

tff(c_135,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_92,c_127])).

tff(c_824,plain,(
    ! [B_220] :
      ( r2_hidden(B_220,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_220)
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_809])).

tff(c_835,plain,(
    ! [B_220] :
      ( r2_hidden(B_220,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_220)
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_824])).

tff(c_837,plain,(
    ! [B_223] :
      ( r2_hidden(B_223,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_223)
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_835])).

tff(c_970,plain,(
    ! [B_236,A_237] :
      ( r2_hidden(B_236,A_237)
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_237))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_236)
      | ~ m1_subset_1(B_236,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_837,c_8])).

tff(c_975,plain,(
    ! [B_238,B_239] :
      ( r2_hidden(B_238,B_239)
      | ~ m1_connsp_2('#skF_4','#skF_3',B_238)
      | ~ m1_subset_1(B_238,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_239) ) ),
    inference(resolution,[status(thm)],[c_18,c_970])).

tff(c_988,plain,(
    ! [B_239] :
      ( r2_hidden('#skF_5',B_239)
      | ~ m1_connsp_2('#skF_4','#skF_3','#skF_5')
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_239) ) ),
    inference(resolution,[status(thm)],[c_135,c_975])).

tff(c_990,plain,(
    ~ m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_988])).

tff(c_5079,plain,(
    ! [B_688,A_689,C_690] :
      ( r2_hidden(B_688,A_689)
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_6'(C_690)),k1_zfmisc_1(A_689))
      | ~ m1_connsp_2('#skF_6'(C_690),'#skF_3',B_688)
      | ~ m1_subset_1(B_688,u1_struct_0('#skF_3'))
      | ~ r2_hidden(C_690,'#skF_4')
      | ~ m1_subset_1(C_690,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_881,c_8])).

tff(c_5084,plain,(
    ! [B_691,B_692,C_693] :
      ( r2_hidden(B_691,B_692)
      | ~ m1_connsp_2('#skF_6'(C_693),'#skF_3',B_691)
      | ~ m1_subset_1(B_691,u1_struct_0('#skF_3'))
      | ~ r2_hidden(C_693,'#skF_4')
      | ~ m1_subset_1(C_693,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_6'(C_693)),B_692) ) ),
    inference(resolution,[status(thm)],[c_18,c_5079])).

tff(c_5111,plain,(
    ! [C_696,B_697] :
      ( r2_hidden(C_696,B_697)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_6'(C_696)),B_697)
      | ~ r2_hidden(C_696,'#skF_4')
      | ~ m1_subset_1(C_696,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_235,c_5084])).

tff(c_5126,plain,(
    ! [C_696,C_28] :
      ( r2_hidden(C_696,k1_tops_1('#skF_3',C_28))
      | ~ r2_hidden(C_696,'#skF_4')
      | ~ m1_subset_1(C_696,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'(C_696),C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_6'(C_696),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_5111])).

tff(c_10502,plain,(
    ! [C_1007,C_1008] :
      ( r2_hidden(C_1007,k1_tops_1('#skF_3',C_1008))
      | ~ r2_hidden(C_1007,'#skF_4')
      | ~ m1_subset_1(C_1007,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'(C_1007),C_1008)
      | ~ m1_subset_1(C_1008,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_6'(C_1007),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5126])).

tff(c_10535,plain,(
    ! [C_1009] :
      ( r2_hidden(C_1009,k1_tops_1('#skF_3','#skF_4'))
      | ~ r2_hidden(C_1009,'#skF_4')
      | ~ m1_subset_1(C_1009,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'(C_1009),'#skF_4')
      | ~ m1_subset_1('#skF_6'(C_1009),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_10502])).

tff(c_10544,plain,(
    ! [C_1010] :
      ( r2_hidden(C_1010,k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_6'(C_1010),'#skF_4')
      | ~ r2_hidden(C_1010,'#skF_4')
      | ~ m1_subset_1(C_1010,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_248,c_10535])).

tff(c_10557,plain,(
    ! [C_1010] :
      ( m1_connsp_2('#skF_4','#skF_3',C_1010)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_6'(C_1010),'#skF_4')
      | ~ r2_hidden(C_1010,'#skF_4')
      | ~ m1_subset_1(C_1010,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10544,c_40])).

tff(c_10583,plain,(
    ! [C_1010] :
      ( m1_connsp_2('#skF_4','#skF_3',C_1010)
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_6'(C_1010),'#skF_4')
      | ~ r2_hidden(C_1010,'#skF_4')
      | ~ m1_subset_1(C_1010,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_10557])).

tff(c_10607,plain,(
    ! [C_1016] :
      ( m1_connsp_2('#skF_4','#skF_3',C_1016)
      | ~ r1_tarski('#skF_6'(C_1016),'#skF_4')
      | ~ r2_hidden(C_1016,'#skF_4')
      | ~ m1_subset_1(C_1016,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10583])).

tff(c_10612,plain,(
    ! [C_1017] :
      ( m1_connsp_2('#skF_4','#skF_3',C_1017)
      | ~ r2_hidden(C_1017,'#skF_4')
      | ~ m1_subset_1(C_1017,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_122,c_10607])).

tff(c_10643,plain,
    ( m1_connsp_2('#skF_4','#skF_3','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_10612])).

tff(c_10659,plain,(
    m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_10643])).

tff(c_10661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_990,c_10659])).

tff(c_10676,plain,(
    ! [B_1020] :
      ( r2_hidden('#skF_5',B_1020)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_1020) ) ),
    inference(splitRight,[status(thm)],[c_988])).

tff(c_10680,plain,(
    ! [C_28] :
      ( r2_hidden('#skF_5',k1_tops_1('#skF_3',C_28))
      | ~ r1_tarski('#skF_4',C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_10676])).

tff(c_10943,plain,(
    ! [C_1034] :
      ( r2_hidden('#skF_5',k1_tops_1('#skF_3',C_1034))
      | ~ r1_tarski('#skF_4',C_1034)
      | ~ m1_subset_1(C_1034,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_10680])).

tff(c_10976,plain,(
    ! [A_1035] :
      ( r2_hidden('#skF_5',k1_tops_1('#skF_3',A_1035))
      | ~ r1_tarski('#skF_4',A_1035)
      | ~ r1_tarski(A_1035,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_10943])).

tff(c_10980,plain,(
    ! [A_1035] :
      ( m1_connsp_2(A_1035,'#skF_3','#skF_5')
      | ~ m1_subset_1(A_1035,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_4',A_1035)
      | ~ r1_tarski(A_1035,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10976,c_40])).

tff(c_10992,plain,(
    ! [A_1035] :
      ( m1_connsp_2(A_1035,'#skF_3','#skF_5')
      | ~ m1_subset_1(A_1035,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_4',A_1035)
      | ~ r1_tarski(A_1035,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_135,c_10980])).

tff(c_11002,plain,(
    ! [A_1036] :
      ( m1_connsp_2(A_1036,'#skF_3','#skF_5')
      | ~ m1_subset_1(A_1036,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_4',A_1036)
      | ~ r1_tarski(A_1036,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10992])).

tff(c_11035,plain,(
    ! [A_1037] :
      ( m1_connsp_2(A_1037,'#skF_3','#skF_5')
      | ~ r1_tarski('#skF_4',A_1037)
      | ~ r1_tarski(A_1037,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_11002])).

tff(c_11065,plain,
    ( m1_connsp_2(u1_struct_0('#skF_3'),'#skF_3','#skF_5')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_11035])).

tff(c_11079,plain,(
    m1_connsp_2(u1_struct_0('#skF_3'),'#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_11065])).

tff(c_832,plain,(
    ! [B_220,A_221,A_14] :
      ( r2_hidden(B_220,k1_tops_1(A_221,A_14))
      | ~ m1_connsp_2(A_14,A_221,B_220)
      | ~ m1_subset_1(B_220,u1_struct_0(A_221))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221)
      | ~ r1_tarski(A_14,u1_struct_0(A_221)) ) ),
    inference(resolution,[status(thm)],[c_18,c_809])).

tff(c_350,plain,(
    ! [A_155,B_156,C_157] :
      ( v3_pre_topc('#skF_2'(A_155,B_156,C_157),A_155)
      | ~ r2_hidden(B_156,k1_tops_1(A_155,C_157))
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_365,plain,(
    ! [A_155,B_156,A_14] :
      ( v3_pre_topc('#skF_2'(A_155,B_156,A_14),A_155)
      | ~ r2_hidden(B_156,k1_tops_1(A_155,A_14))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | ~ r1_tarski(A_14,u1_struct_0(A_155)) ) ),
    inference(resolution,[status(thm)],[c_18,c_350])).

tff(c_30,plain,(
    ! [A_29,B_36,C_37] :
      ( r1_tarski('#skF_2'(A_29,B_36,C_37),C_37)
      | ~ r2_hidden(B_36,k1_tops_1(A_29,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10984,plain,(
    ! [A_1035] :
      ( r1_tarski('#skF_2'('#skF_3','#skF_5',A_1035),A_1035)
      | ~ m1_subset_1(A_1035,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r1_tarski('#skF_4',A_1035)
      | ~ r1_tarski(A_1035,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10976,c_30])).

tff(c_11848,plain,(
    ! [A_1099] :
      ( r1_tarski('#skF_2'('#skF_3','#skF_5',A_1099),A_1099)
      | ~ m1_subset_1(A_1099,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_4',A_1099)
      | ~ r1_tarski(A_1099,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_10984])).

tff(c_11875,plain,(
    ! [A_1100] :
      ( r1_tarski('#skF_2'('#skF_3','#skF_5',A_1100),A_1100)
      | ~ r1_tarski('#skF_4',A_1100)
      | ~ r1_tarski(A_1100,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_11848])).

tff(c_10742,plain,(
    ! [B_1021,A_1022,C_1023] :
      ( m1_connsp_2(B_1021,A_1022,C_1023)
      | ~ r2_hidden(C_1023,B_1021)
      | ~ v3_pre_topc(B_1021,A_1022)
      | ~ m1_subset_1(C_1023,u1_struct_0(A_1022))
      | ~ m1_subset_1(B_1021,k1_zfmisc_1(u1_struct_0(A_1022)))
      | ~ l1_pre_topc(A_1022)
      | ~ v2_pre_topc(A_1022)
      | v2_struct_0(A_1022) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_10750,plain,(
    ! [B_1021] :
      ( m1_connsp_2(B_1021,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_1021)
      | ~ v3_pre_topc(B_1021,'#skF_3')
      | ~ m1_subset_1(B_1021,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_135,c_10742])).

tff(c_10757,plain,(
    ! [B_1021] :
      ( m1_connsp_2(B_1021,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_1021)
      | ~ v3_pre_topc(B_1021,'#skF_3')
      | ~ m1_subset_1(B_1021,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_10750])).

tff(c_10794,plain,(
    ! [B_1026] :
      ( m1_connsp_2(B_1026,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_1026)
      | ~ v3_pre_topc(B_1026,'#skF_3')
      | ~ m1_subset_1(B_1026,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10757])).

tff(c_10823,plain,(
    ! [A_14] :
      ( m1_connsp_2(A_14,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',A_14)
      | ~ v3_pre_topc(A_14,'#skF_3')
      | ~ r1_tarski(A_14,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_10794])).

tff(c_11900,plain,
    ( m1_connsp_2('#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')),'#skF_3','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')))
    | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')),'#skF_3')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3'))
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_11875,c_10823])).

tff(c_11948,plain,
    ( m1_connsp_2('#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')),'#skF_3','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')))
    | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92,c_11900])).

tff(c_12371,plain,(
    ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11948])).

tff(c_12378,plain,
    ( ~ r2_hidden('#skF_5',k1_tops_1('#skF_3',u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_365,c_12371])).

tff(c_12381,plain,(
    ~ r2_hidden('#skF_5',k1_tops_1('#skF_3',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50,c_48,c_12378])).

tff(c_12384,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_3'),'#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_832,c_12381])).

tff(c_12393,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50,c_48,c_135,c_11079,c_12384])).

tff(c_12395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_12393])).

tff(c_12397,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_11948])).

tff(c_34,plain,(
    ! [A_29,B_36,C_37] :
      ( m1_subset_1('#skF_2'(A_29,B_36,C_37),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ r2_hidden(B_36,k1_tops_1(A_29,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    ! [B_49,D_55,C_53,A_41] :
      ( k1_tops_1(B_49,D_55) = D_55
      | ~ v3_pre_topc(D_55,B_49)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(B_49)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(B_49)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_586,plain,(
    ! [C_204,A_205] :
      ( ~ m1_subset_1(C_204,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_604,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_586])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_604])).

tff(c_616,plain,(
    ! [B_206,D_207] :
      ( k1_tops_1(B_206,D_207) = D_207
      | ~ v3_pre_topc(D_207,B_206)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(u1_struct_0(B_206)))
      | ~ l1_pre_topc(B_206) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_639,plain,(
    ! [A_29,B_36,C_37] :
      ( k1_tops_1(A_29,'#skF_2'(A_29,B_36,C_37)) = '#skF_2'(A_29,B_36,C_37)
      | ~ v3_pre_topc('#skF_2'(A_29,B_36,C_37),A_29)
      | ~ r2_hidden(B_36,k1_tops_1(A_29,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_616])).

tff(c_12399,plain,
    ( k1_tops_1('#skF_3','#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3'))) = '#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_5',k1_tops_1('#skF_3',u1_struct_0('#skF_3')))
    | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12397,c_639])).

tff(c_12402,plain,
    ( k1_tops_1('#skF_3','#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3'))) = '#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_5',k1_tops_1('#skF_3',u1_struct_0('#skF_3')))
    | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_12399])).

tff(c_14963,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_12402])).

tff(c_14967,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_14963])).

tff(c_14971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14967])).

tff(c_14973,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_12402])).

tff(c_20,plain,(
    ! [A_16,C_18,B_17] :
      ( m1_subset_1(A_16,C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(C_18))
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_15105,plain,(
    ! [A_16] :
      ( m1_subset_1(A_16,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_16,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14973,c_20])).

tff(c_18784,plain,(
    ! [A_1530,C_1531] :
      ( m1_subset_1('#skF_1'(A_1530,'#skF_4',C_1531),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_4',C_1531)
      | ~ m1_subset_1(C_1531,k1_zfmisc_1(A_1530))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1530))
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18753,c_15105])).

tff(c_18848,plain,(
    ! [A_1530,C_1531] :
      ( m1_subset_1('#skF_1'(A_1530,'#skF_4',C_1531),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_4',C_1531)
      | ~ m1_subset_1(C_1531,k1_zfmisc_1(A_1530))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1530)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18784])).

tff(c_20952,plain,(
    ! [B_1618,A_1619] :
      ( r1_tarski(B_1618,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_1619))
      | ~ m1_subset_1(B_1618,k1_zfmisc_1(A_1619))
      | ~ m1_connsp_2('#skF_4','#skF_3','#skF_1'(A_1619,B_1618,k1_tops_1('#skF_3','#skF_4')))
      | ~ m1_subset_1('#skF_1'(A_1619,B_1618,k1_tops_1('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_837,c_10])).

tff(c_20960,plain,(
    ! [A_1530] :
      ( ~ m1_connsp_2('#skF_4','#skF_3','#skF_1'(A_1530,'#skF_4',k1_tops_1('#skF_3','#skF_4')))
      | r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_1530))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1530)) ) ),
    inference(resolution,[status(thm)],[c_18848,c_20952])).

tff(c_20991,plain,(
    ! [A_1530] :
      ( ~ m1_connsp_2('#skF_4','#skF_3','#skF_1'(A_1530,'#skF_4',k1_tops_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_1530))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1530)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_198,c_20960])).

tff(c_43554,plain,(
    ! [A_2504] :
      ( ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_2504))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2504))
      | ~ r2_hidden('#skF_1'(A_2504,'#skF_4',k1_tops_1('#skF_3','#skF_4')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40005,c_20991])).

tff(c_43578,plain,(
    ! [A_1556] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_1556))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1556))
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_19494,c_43554])).

tff(c_43605,plain,(
    ! [A_1556] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_1556))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1556)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_43578])).

tff(c_43615,plain,(
    ! [A_2505] :
      ( ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_2505))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2505)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_43605])).

tff(c_43762,plain,(
    ! [B_2510] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(B_2510))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2510) ) ),
    inference(resolution,[status(thm)],[c_18,c_43615])).

tff(c_43809,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20525,c_43762])).

tff(c_43852,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_6,c_43809])).

tff(c_43866,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_43852])).

tff(c_43870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_43866])).

tff(c_43871,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_44201,plain,(
    ! [A_2582,B_2583,C_2584] :
      ( r1_tarski(k1_tops_1(A_2582,B_2583),k1_tops_1(A_2582,C_2584))
      | ~ r1_tarski(B_2583,C_2584)
      | ~ m1_subset_1(C_2584,k1_zfmisc_1(u1_struct_0(A_2582)))
      | ~ m1_subset_1(B_2583,k1_zfmisc_1(u1_struct_0(A_2582)))
      | ~ l1_pre_topc(A_2582) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44212,plain,(
    ! [C_2584] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_3',C_2584))
      | ~ r1_tarski('#skF_4',C_2584)
      | ~ m1_subset_1(C_2584,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43871,c_44201])).

tff(c_44223,plain,(
    ! [C_2585] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_3',C_2585))
      | ~ r1_tarski('#skF_4',C_2585)
      | ~ m1_subset_1(C_2585,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44212])).

tff(c_44251,plain,(
    ! [A_2586] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_3',A_2586))
      | ~ r1_tarski('#skF_4',A_2586)
      | ~ r1_tarski(A_2586,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_44223])).

tff(c_44264,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_3',u1_struct_0('#skF_3')))
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_44251])).

tff(c_44273,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_3',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_44264])).

tff(c_137,plain,(
    ! [C_109,A_110,B_111] :
      ( r2_hidden(C_109,A_110)
      | ~ r2_hidden(C_109,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_141,plain,(
    ! [A_112] :
      ( r2_hidden('#skF_5',A_112)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_112)) ) ),
    inference(resolution,[status(thm)],[c_93,c_137])).

tff(c_170,plain,(
    ! [B_115] :
      ( r2_hidden('#skF_5',B_115)
      | ~ r1_tarski('#skF_4',B_115) ) ),
    inference(resolution,[status(thm)],[c_18,c_141])).

tff(c_43893,plain,(
    ! [A_2513,B_2514] :
      ( r2_hidden('#skF_5',A_2513)
      | ~ m1_subset_1(B_2514,k1_zfmisc_1(A_2513))
      | ~ r1_tarski('#skF_4',B_2514) ) ),
    inference(resolution,[status(thm)],[c_170,c_8])).

tff(c_43900,plain,(
    ! [B_15,A_14] :
      ( r2_hidden('#skF_5',B_15)
      | ~ r1_tarski('#skF_4',A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_43893])).

tff(c_44295,plain,(
    ! [B_2587] :
      ( r2_hidden('#skF_5',B_2587)
      | ~ r1_tarski(k1_tops_1('#skF_3',u1_struct_0('#skF_3')),B_2587) ) ),
    inference(resolution,[status(thm)],[c_44273,c_43900])).

tff(c_44314,plain,(
    r2_hidden('#skF_5',k1_tops_1('#skF_3',u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6,c_44295])).

tff(c_28,plain,(
    ! [B_36,A_29,C_37] :
      ( r2_hidden(B_36,'#skF_2'(A_29,B_36,C_37))
      | ~ r2_hidden(B_36,k1_tops_1(A_29,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44316,plain,
    ( r2_hidden('#skF_5','#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')))
    | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44314,c_28])).

tff(c_44325,plain,
    ( r2_hidden('#skF_5','#skF_2'('#skF_3','#skF_5',u1_struct_0('#skF_3')))
    | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44316])).

tff(c_44471,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_44325])).

tff(c_44474,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_44471])).

tff(c_44478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_44474])).

tff(c_44480,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_44325])).

tff(c_36,plain,(
    ! [C_53,A_41,D_55,B_49] :
      ( v3_pre_topc(C_53,A_41)
      | k1_tops_1(A_41,C_53) != C_53
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(B_49)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(B_49)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44639,plain,(
    ! [D_2599,B_2600] :
      ( ~ m1_subset_1(D_2599,k1_zfmisc_1(u1_struct_0(B_2600)))
      | ~ l1_pre_topc(B_2600) ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_44642,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44480,c_44639])).

tff(c_44660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44642])).

tff(c_44716,plain,(
    ! [C_2606,A_2607] :
      ( v3_pre_topc(C_2606,A_2607)
      | k1_tops_1(A_2607,C_2606) != C_2606
      | ~ m1_subset_1(C_2606,k1_zfmisc_1(u1_struct_0(A_2607)))
      | ~ l1_pre_topc(A_2607)
      | ~ v2_pre_topc(A_2607) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_44736,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_44716])).

tff(c_44749,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_43871,c_44736])).

tff(c_44751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_44749])).

tff(c_44753,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [D_90] :
      ( ~ r1_tarski(D_90,'#skF_4')
      | ~ m1_connsp_2(D_90,'#skF_3','#skF_5')
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_44851,plain,(
    ! [D_2630] :
      ( ~ r1_tarski(D_2630,'#skF_4')
      | ~ m1_connsp_2(D_2630,'#skF_3','#skF_5')
      | ~ m1_subset_1(D_2630,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44753,c_54])).

tff(c_44858,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_44851])).

tff(c_44862,plain,(
    ~ m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_44858])).

tff(c_44752,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,
    ( m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_44755,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44753,c_58])).

tff(c_45226,plain,(
    ! [C_2706,A_2707] :
      ( ~ m1_subset_1(C_2706,k1_zfmisc_1(u1_struct_0(A_2707)))
      | ~ l1_pre_topc(A_2707)
      | ~ v2_pre_topc(A_2707) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_45241,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_45226])).

tff(c_45248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_45241])).

tff(c_45250,plain,(
    ! [B_2708,D_2709] :
      ( k1_tops_1(B_2708,D_2709) = D_2709
      | ~ v3_pre_topc(D_2709,B_2708)
      | ~ m1_subset_1(D_2709,k1_zfmisc_1(u1_struct_0(B_2708)))
      | ~ l1_pre_topc(B_2708) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_45268,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_45250])).

tff(c_45275,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44753,c_45268])).

tff(c_44822,plain,(
    ! [A_2626,B_2627] :
      ( r1_tarski(k1_tops_1(A_2626,B_2627),B_2627)
      | ~ m1_subset_1(B_2627,k1_zfmisc_1(u1_struct_0(A_2626)))
      | ~ l1_pre_topc(A_2626) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44827,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_44822])).

tff(c_44831,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44827])).

tff(c_44834,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44831,c_2])).

tff(c_44876,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44834])).

tff(c_45277,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45275,c_44876])).

tff(c_45281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_45277])).

tff(c_45282,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44834])).

tff(c_46277,plain,(
    ! [C_2807,A_2808,B_2809] :
      ( m1_connsp_2(C_2807,A_2808,B_2809)
      | ~ r2_hidden(B_2809,k1_tops_1(A_2808,C_2807))
      | ~ m1_subset_1(C_2807,k1_zfmisc_1(u1_struct_0(A_2808)))
      | ~ m1_subset_1(B_2809,u1_struct_0(A_2808))
      | ~ l1_pre_topc(A_2808)
      | ~ v2_pre_topc(A_2808)
      | v2_struct_0(A_2808) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46286,plain,(
    ! [B_2809] :
      ( m1_connsp_2('#skF_4','#skF_3',B_2809)
      | ~ r2_hidden(B_2809,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_2809,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45282,c_46277])).

tff(c_46300,plain,(
    ! [B_2809] :
      ( m1_connsp_2('#skF_4','#skF_3',B_2809)
      | ~ r2_hidden(B_2809,'#skF_4')
      | ~ m1_subset_1(B_2809,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_46286])).

tff(c_46303,plain,(
    ! [B_2810] :
      ( m1_connsp_2('#skF_4','#skF_3',B_2810)
      | ~ r2_hidden(B_2810,'#skF_4')
      | ~ m1_subset_1(B_2810,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46300])).

tff(c_46313,plain,
    ( m1_connsp_2('#skF_4','#skF_3','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44755,c_46303])).

tff(c_46318,plain,(
    m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44752,c_46313])).

tff(c_46320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44862,c_46318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:36:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.86/12.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.86/12.65  
% 20.86/12.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.86/12.65  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 20.86/12.65  
% 20.86/12.65  %Foreground sorts:
% 20.86/12.65  
% 20.86/12.65  
% 20.86/12.65  %Background operators:
% 20.86/12.65  
% 20.86/12.65  
% 20.86/12.65  %Foreground operators:
% 20.86/12.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 20.86/12.65  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 20.86/12.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 20.86/12.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 20.86/12.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.86/12.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.86/12.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.86/12.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.86/12.65  tff('#skF_5', type, '#skF_5': $i).
% 20.86/12.65  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 20.86/12.65  tff('#skF_3', type, '#skF_3': $i).
% 20.86/12.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.86/12.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.86/12.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.86/12.65  tff('#skF_4', type, '#skF_4': $i).
% 20.86/12.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.86/12.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.86/12.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.86/12.65  tff('#skF_6', type, '#skF_6': $i > $i).
% 20.86/12.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.86/12.65  
% 21.09/12.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.09/12.68  tff(f_183, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 21.09/12.68  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 21.09/12.68  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 21.09/12.68  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 21.09/12.68  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 21.09/12.68  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 21.09/12.68  tff(f_62, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 21.09/12.68  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 21.09/12.68  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 21.09/12.68  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 21.09/12.68  tff(f_120, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 21.09/12.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.09/12.68  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_56, plain, (r2_hidden('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_87, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 21.09/12.68  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 21.09/12.68  tff(c_88, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | ~m1_subset_1(A_94, k1_zfmisc_1(B_95)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 21.09/12.68  tff(c_92, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_88])).
% 21.09/12.68  tff(c_151, plain, (![A_113, B_114]: (r1_tarski(k1_tops_1(A_113, B_114), B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_69])).
% 21.09/12.68  tff(c_157, plain, (![A_113, A_14]: (r1_tarski(k1_tops_1(A_113, A_14), A_14) | ~l1_pre_topc(A_113) | ~r1_tarski(A_14, u1_struct_0(A_113)))), inference(resolution, [status(thm)], [c_18, c_151])).
% 21.09/12.68  tff(c_24, plain, (![A_22, B_26, C_28]: (r1_tarski(k1_tops_1(A_22, B_26), k1_tops_1(A_22, C_28)) | ~r1_tarski(B_26, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.09/12.68  tff(c_156, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_151])).
% 21.09/12.68  tff(c_160, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_156])).
% 21.09/12.68  tff(c_292, plain, (![A_139, B_140, C_141]: (r2_hidden('#skF_1'(A_139, B_140, C_141), B_140) | r1_tarski(B_140, C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(A_139)) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.09/12.68  tff(c_8, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 21.09/12.68  tff(c_500, plain, (![A_184, B_185, C_186, A_187]: (r2_hidden('#skF_1'(A_184, B_185, C_186), A_187) | ~m1_subset_1(B_185, k1_zfmisc_1(A_187)) | r1_tarski(B_185, C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(A_184)) | ~m1_subset_1(B_185, k1_zfmisc_1(A_184)))), inference(resolution, [status(thm)], [c_292, c_8])).
% 21.09/12.68  tff(c_15620, plain, (![A_1371, B_1373, A_1372, A_1370, C_1369]: (r2_hidden('#skF_1'(A_1372, B_1373, C_1369), A_1371) | ~m1_subset_1(A_1370, k1_zfmisc_1(A_1371)) | ~m1_subset_1(B_1373, k1_zfmisc_1(A_1370)) | r1_tarski(B_1373, C_1369) | ~m1_subset_1(C_1369, k1_zfmisc_1(A_1372)) | ~m1_subset_1(B_1373, k1_zfmisc_1(A_1372)))), inference(resolution, [status(thm)], [c_500, c_8])).
% 21.09/12.68  tff(c_18722, plain, (![A_1527, A_1529, B_1528, B_1525, C_1526]: (r2_hidden('#skF_1'(A_1527, B_1525, C_1526), B_1528) | ~m1_subset_1(B_1525, k1_zfmisc_1(A_1529)) | r1_tarski(B_1525, C_1526) | ~m1_subset_1(C_1526, k1_zfmisc_1(A_1527)) | ~m1_subset_1(B_1525, k1_zfmisc_1(A_1527)) | ~r1_tarski(A_1529, B_1528))), inference(resolution, [status(thm)], [c_18, c_15620])).
% 21.09/12.68  tff(c_19422, plain, (![B_1555, C_1559, A_1558, B_1557, A_1556]: (r2_hidden('#skF_1'(A_1556, A_1558, C_1559), B_1555) | r1_tarski(A_1558, C_1559) | ~m1_subset_1(C_1559, k1_zfmisc_1(A_1556)) | ~m1_subset_1(A_1558, k1_zfmisc_1(A_1556)) | ~r1_tarski(B_1557, B_1555) | ~r1_tarski(A_1558, B_1557))), inference(resolution, [status(thm)], [c_18, c_18722])).
% 21.09/12.68  tff(c_19851, plain, (![A_1579, A_1580, C_1581]: (r2_hidden('#skF_1'(A_1579, A_1580, C_1581), '#skF_4') | r1_tarski(A_1580, C_1581) | ~m1_subset_1(C_1581, k1_zfmisc_1(A_1579)) | ~m1_subset_1(A_1580, k1_zfmisc_1(A_1579)) | ~r1_tarski(A_1580, k1_tops_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_160, c_19422])).
% 21.09/12.68  tff(c_10, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.09/12.68  tff(c_19866, plain, (![A_1582, A_1583]: (r1_tarski(A_1582, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1583)) | ~m1_subset_1(A_1582, k1_zfmisc_1(A_1583)) | ~r1_tarski(A_1582, k1_tops_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_19851, c_10])).
% 21.09/12.68  tff(c_19978, plain, (![A_1588, B_1589]: (r1_tarski(A_1588, '#skF_4') | ~m1_subset_1(A_1588, k1_zfmisc_1(B_1589)) | ~r1_tarski(A_1588, k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_1589))), inference(resolution, [status(thm)], [c_18, c_19866])).
% 21.09/12.68  tff(c_20023, plain, (![A_1590, B_1591]: (r1_tarski(A_1590, '#skF_4') | ~r1_tarski(A_1590, k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_1591) | ~r1_tarski(A_1590, B_1591))), inference(resolution, [status(thm)], [c_18, c_19978])).
% 21.09/12.68  tff(c_20035, plain, (![B_26, B_1591]: (r1_tarski(k1_tops_1('#skF_3', B_26), '#skF_4') | ~r1_tarski('#skF_4', B_1591) | ~r1_tarski(k1_tops_1('#skF_3', B_26), B_1591) | ~r1_tarski(B_26, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_20023])).
% 21.09/12.68  tff(c_20174, plain, (![B_1595, B_1596]: (r1_tarski(k1_tops_1('#skF_3', B_1595), '#skF_4') | ~r1_tarski('#skF_4', B_1596) | ~r1_tarski(k1_tops_1('#skF_3', B_1595), B_1596) | ~r1_tarski(B_1595, '#skF_4') | ~m1_subset_1(B_1595, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_20035])).
% 21.09/12.68  tff(c_20202, plain, (![A_14]: (r1_tarski(k1_tops_1('#skF_3', A_14), '#skF_4') | ~r1_tarski('#skF_4', A_14) | ~r1_tarski(A_14, '#skF_4') | ~m1_subset_1(A_14, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_14, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_157, c_20174])).
% 21.09/12.68  tff(c_20473, plain, (![A_1602]: (r1_tarski(k1_tops_1('#skF_3', A_1602), '#skF_4') | ~r1_tarski('#skF_4', A_1602) | ~r1_tarski(A_1602, '#skF_4') | ~m1_subset_1(A_1602, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_1602, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20202])).
% 21.09/12.68  tff(c_20525, plain, (![A_14]: (r1_tarski(k1_tops_1('#skF_3', A_14), '#skF_4') | ~r1_tarski('#skF_4', A_14) | ~r1_tarski(A_14, '#skF_4') | ~r1_tarski(A_14, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_20473])).
% 21.09/12.68  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.09/12.68  tff(c_169, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_160, c_2])).
% 21.09/12.68  tff(c_198, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_169])).
% 21.09/12.68  tff(c_19494, plain, (![A_1556, A_1558, C_1559, B_2]: (r2_hidden('#skF_1'(A_1556, A_1558, C_1559), B_2) | r1_tarski(A_1558, C_1559) | ~m1_subset_1(C_1559, k1_zfmisc_1(A_1556)) | ~m1_subset_1(A_1558, k1_zfmisc_1(A_1556)) | ~r1_tarski(A_1558, B_2))), inference(resolution, [status(thm)], [c_6, c_19422])).
% 21.09/12.68  tff(c_110, plain, (![A_100, C_101, B_102]: (m1_subset_1(A_100, C_101) | ~m1_subset_1(B_102, k1_zfmisc_1(C_101)) | ~r2_hidden(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_62])).
% 21.09/12.68  tff(c_116, plain, (![A_100]: (m1_subset_1(A_100, u1_struct_0('#skF_3')) | ~r2_hidden(A_100, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_110])).
% 21.09/12.68  tff(c_68, plain, (![C_91]: (v3_pre_topc('#skF_4', '#skF_3') | r1_tarski('#skF_6'(C_91), '#skF_4') | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_122, plain, (![C_91]: (r1_tarski('#skF_6'(C_91), '#skF_4') | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_87, c_68])).
% 21.09/12.68  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_84, plain, (![C_91]: (v3_pre_topc('#skF_4', '#skF_3') | m1_subset_1('#skF_6'(C_91), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_248, plain, (![C_91]: (m1_subset_1('#skF_6'(C_91), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_87, c_84])).
% 21.09/12.68  tff(c_76, plain, (![C_91]: (v3_pre_topc('#skF_4', '#skF_3') | m1_connsp_2('#skF_6'(C_91), '#skF_3', C_91) | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_235, plain, (![C_91]: (m1_connsp_2('#skF_6'(C_91), '#skF_3', C_91) | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_87, c_76])).
% 21.09/12.68  tff(c_809, plain, (![B_220, A_221, C_222]: (r2_hidden(B_220, k1_tops_1(A_221, C_222)) | ~m1_connsp_2(C_222, A_221, B_220) | ~m1_subset_1(C_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~m1_subset_1(B_220, u1_struct_0(A_221)) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_137])).
% 21.09/12.68  tff(c_819, plain, (![B_220, C_91]: (r2_hidden(B_220, k1_tops_1('#skF_3', '#skF_6'(C_91))) | ~m1_connsp_2('#skF_6'(C_91), '#skF_3', B_220) | ~m1_subset_1(B_220, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_248, c_809])).
% 21.09/12.68  tff(c_830, plain, (![B_220, C_91]: (r2_hidden(B_220, k1_tops_1('#skF_3', '#skF_6'(C_91))) | ~m1_connsp_2('#skF_6'(C_91), '#skF_3', B_220) | ~m1_subset_1(B_220, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_819])).
% 21.09/12.68  tff(c_881, plain, (![B_226, C_227]: (r2_hidden(B_226, k1_tops_1('#skF_3', '#skF_6'(C_227))) | ~m1_connsp_2('#skF_6'(C_227), '#skF_3', B_226) | ~m1_subset_1(B_226, u1_struct_0('#skF_3')) | ~r2_hidden(C_227, '#skF_4') | ~m1_subset_1(C_227, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_830])).
% 21.09/12.68  tff(c_16381, plain, (![B_1400, A_1401, C_1402]: (r2_hidden(B_1400, A_1401) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_6'(C_1402)), k1_zfmisc_1(A_1401)) | ~m1_connsp_2('#skF_6'(C_1402), '#skF_3', B_1400) | ~m1_subset_1(B_1400, u1_struct_0('#skF_3')) | ~r2_hidden(C_1402, '#skF_4') | ~m1_subset_1(C_1402, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_881, c_8])).
% 21.09/12.68  tff(c_24187, plain, (![B_1742, B_1743, C_1744]: (r2_hidden(B_1742, B_1743) | ~m1_connsp_2('#skF_6'(C_1744), '#skF_3', B_1742) | ~m1_subset_1(B_1742, u1_struct_0('#skF_3')) | ~r2_hidden(C_1744, '#skF_4') | ~m1_subset_1(C_1744, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_6'(C_1744)), B_1743))), inference(resolution, [status(thm)], [c_18, c_16381])).
% 21.09/12.68  tff(c_24230, plain, (![C_1745, B_1746]: (r2_hidden(C_1745, B_1746) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_6'(C_1745)), B_1746) | ~r2_hidden(C_1745, '#skF_4') | ~m1_subset_1(C_1745, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_235, c_24187])).
% 21.09/12.68  tff(c_24257, plain, (![C_1745, C_28]: (r2_hidden(C_1745, k1_tops_1('#skF_3', C_28)) | ~r2_hidden(C_1745, '#skF_4') | ~m1_subset_1(C_1745, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'(C_1745), C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6'(C_1745), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_24230])).
% 21.09/12.68  tff(c_39809, plain, (![C_2414, C_2415]: (r2_hidden(C_2414, k1_tops_1('#skF_3', C_2415)) | ~r2_hidden(C_2414, '#skF_4') | ~m1_subset_1(C_2414, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'(C_2414), C_2415) | ~m1_subset_1(C_2415, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6'(C_2414), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24257])).
% 21.09/12.68  tff(c_39857, plain, (![C_2416]: (r2_hidden(C_2416, k1_tops_1('#skF_3', '#skF_4')) | ~r2_hidden(C_2416, '#skF_4') | ~m1_subset_1(C_2416, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'(C_2416), '#skF_4') | ~m1_subset_1('#skF_6'(C_2416), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_46, c_39809])).
% 21.09/12.68  tff(c_39866, plain, (![C_2417]: (r2_hidden(C_2417, k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_6'(C_2417), '#skF_4') | ~r2_hidden(C_2417, '#skF_4') | ~m1_subset_1(C_2417, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_248, c_39857])).
% 21.09/12.68  tff(c_40, plain, (![C_62, A_56, B_60]: (m1_connsp_2(C_62, A_56, B_60) | ~r2_hidden(B_60, k1_tops_1(A_56, C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_60, u1_struct_0(A_56)) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_137])).
% 21.09/12.68  tff(c_39883, plain, (![C_2417]: (m1_connsp_2('#skF_4', '#skF_3', C_2417) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_6'(C_2417), '#skF_4') | ~r2_hidden(C_2417, '#skF_4') | ~m1_subset_1(C_2417, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_39866, c_40])).
% 21.09/12.68  tff(c_39912, plain, (![C_2417]: (m1_connsp_2('#skF_4', '#skF_3', C_2417) | v2_struct_0('#skF_3') | ~r1_tarski('#skF_6'(C_2417), '#skF_4') | ~r2_hidden(C_2417, '#skF_4') | ~m1_subset_1(C_2417, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_39883])).
% 21.09/12.68  tff(c_39923, plain, (![C_2418]: (m1_connsp_2('#skF_4', '#skF_3', C_2418) | ~r1_tarski('#skF_6'(C_2418), '#skF_4') | ~r2_hidden(C_2418, '#skF_4') | ~m1_subset_1(C_2418, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_39912])).
% 21.09/12.68  tff(c_39928, plain, (![C_2419]: (m1_connsp_2('#skF_4', '#skF_3', C_2419) | ~r2_hidden(C_2419, '#skF_4') | ~m1_subset_1(C_2419, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_122, c_39923])).
% 21.09/12.68  tff(c_40005, plain, (![A_2420]: (m1_connsp_2('#skF_4', '#skF_3', A_2420) | ~r2_hidden(A_2420, '#skF_4'))), inference(resolution, [status(thm)], [c_116, c_39928])).
% 21.09/12.68  tff(c_18753, plain, (![A_1530, C_1531, B_1532]: (r2_hidden('#skF_1'(A_1530, '#skF_4', C_1531), B_1532) | r1_tarski('#skF_4', C_1531) | ~m1_subset_1(C_1531, k1_zfmisc_1(A_1530)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1530)) | ~r1_tarski(u1_struct_0('#skF_3'), B_1532))), inference(resolution, [status(thm)], [c_46, c_18722])).
% 21.09/12.68  tff(c_64, plain, (![C_91]: (r2_hidden('#skF_5', '#skF_4') | r1_tarski('#skF_6'(C_91), '#skF_4') | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.68  tff(c_93, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 21.09/12.68  tff(c_118, plain, (![A_104, B_105, A_106]: (m1_subset_1(A_104, B_105) | ~r2_hidden(A_104, A_106) | ~r1_tarski(A_106, B_105))), inference(resolution, [status(thm)], [c_18, c_110])).
% 21.09/12.68  tff(c_127, plain, (![B_108]: (m1_subset_1('#skF_5', B_108) | ~r1_tarski('#skF_4', B_108))), inference(resolution, [status(thm)], [c_93, c_118])).
% 21.09/12.68  tff(c_135, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_92, c_127])).
% 21.09/12.68  tff(c_824, plain, (![B_220]: (r2_hidden(B_220, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_220) | ~m1_subset_1(B_220, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_809])).
% 21.09/12.68  tff(c_835, plain, (![B_220]: (r2_hidden(B_220, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_220) | ~m1_subset_1(B_220, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_824])).
% 21.09/12.68  tff(c_837, plain, (![B_223]: (r2_hidden(B_223, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_223) | ~m1_subset_1(B_223, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_835])).
% 21.09/12.68  tff(c_970, plain, (![B_236, A_237]: (r2_hidden(B_236, A_237) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_237)) | ~m1_connsp_2('#skF_4', '#skF_3', B_236) | ~m1_subset_1(B_236, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_837, c_8])).
% 21.09/12.68  tff(c_975, plain, (![B_238, B_239]: (r2_hidden(B_238, B_239) | ~m1_connsp_2('#skF_4', '#skF_3', B_238) | ~m1_subset_1(B_238, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_239))), inference(resolution, [status(thm)], [c_18, c_970])).
% 21.09/12.68  tff(c_988, plain, (![B_239]: (r2_hidden('#skF_5', B_239) | ~m1_connsp_2('#skF_4', '#skF_3', '#skF_5') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_239))), inference(resolution, [status(thm)], [c_135, c_975])).
% 21.09/12.68  tff(c_990, plain, (~m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_988])).
% 21.09/12.68  tff(c_5079, plain, (![B_688, A_689, C_690]: (r2_hidden(B_688, A_689) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_6'(C_690)), k1_zfmisc_1(A_689)) | ~m1_connsp_2('#skF_6'(C_690), '#skF_3', B_688) | ~m1_subset_1(B_688, u1_struct_0('#skF_3')) | ~r2_hidden(C_690, '#skF_4') | ~m1_subset_1(C_690, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_881, c_8])).
% 21.09/12.68  tff(c_5084, plain, (![B_691, B_692, C_693]: (r2_hidden(B_691, B_692) | ~m1_connsp_2('#skF_6'(C_693), '#skF_3', B_691) | ~m1_subset_1(B_691, u1_struct_0('#skF_3')) | ~r2_hidden(C_693, '#skF_4') | ~m1_subset_1(C_693, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_6'(C_693)), B_692))), inference(resolution, [status(thm)], [c_18, c_5079])).
% 21.09/12.68  tff(c_5111, plain, (![C_696, B_697]: (r2_hidden(C_696, B_697) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_6'(C_696)), B_697) | ~r2_hidden(C_696, '#skF_4') | ~m1_subset_1(C_696, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_235, c_5084])).
% 21.09/12.68  tff(c_5126, plain, (![C_696, C_28]: (r2_hidden(C_696, k1_tops_1('#skF_3', C_28)) | ~r2_hidden(C_696, '#skF_4') | ~m1_subset_1(C_696, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'(C_696), C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6'(C_696), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_5111])).
% 21.09/12.68  tff(c_10502, plain, (![C_1007, C_1008]: (r2_hidden(C_1007, k1_tops_1('#skF_3', C_1008)) | ~r2_hidden(C_1007, '#skF_4') | ~m1_subset_1(C_1007, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'(C_1007), C_1008) | ~m1_subset_1(C_1008, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6'(C_1007), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5126])).
% 21.09/12.68  tff(c_10535, plain, (![C_1009]: (r2_hidden(C_1009, k1_tops_1('#skF_3', '#skF_4')) | ~r2_hidden(C_1009, '#skF_4') | ~m1_subset_1(C_1009, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'(C_1009), '#skF_4') | ~m1_subset_1('#skF_6'(C_1009), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_46, c_10502])).
% 21.09/12.68  tff(c_10544, plain, (![C_1010]: (r2_hidden(C_1010, k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_6'(C_1010), '#skF_4') | ~r2_hidden(C_1010, '#skF_4') | ~m1_subset_1(C_1010, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_248, c_10535])).
% 21.09/12.68  tff(c_10557, plain, (![C_1010]: (m1_connsp_2('#skF_4', '#skF_3', C_1010) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_6'(C_1010), '#skF_4') | ~r2_hidden(C_1010, '#skF_4') | ~m1_subset_1(C_1010, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10544, c_40])).
% 21.09/12.68  tff(c_10583, plain, (![C_1010]: (m1_connsp_2('#skF_4', '#skF_3', C_1010) | v2_struct_0('#skF_3') | ~r1_tarski('#skF_6'(C_1010), '#skF_4') | ~r2_hidden(C_1010, '#skF_4') | ~m1_subset_1(C_1010, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_10557])).
% 21.09/12.68  tff(c_10607, plain, (![C_1016]: (m1_connsp_2('#skF_4', '#skF_3', C_1016) | ~r1_tarski('#skF_6'(C_1016), '#skF_4') | ~r2_hidden(C_1016, '#skF_4') | ~m1_subset_1(C_1016, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_10583])).
% 21.09/12.68  tff(c_10612, plain, (![C_1017]: (m1_connsp_2('#skF_4', '#skF_3', C_1017) | ~r2_hidden(C_1017, '#skF_4') | ~m1_subset_1(C_1017, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_122, c_10607])).
% 21.09/12.68  tff(c_10643, plain, (m1_connsp_2('#skF_4', '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_135, c_10612])).
% 21.09/12.68  tff(c_10659, plain, (m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_10643])).
% 21.09/12.68  tff(c_10661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_990, c_10659])).
% 21.09/12.68  tff(c_10676, plain, (![B_1020]: (r2_hidden('#skF_5', B_1020) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_1020))), inference(splitRight, [status(thm)], [c_988])).
% 21.09/12.68  tff(c_10680, plain, (![C_28]: (r2_hidden('#skF_5', k1_tops_1('#skF_3', C_28)) | ~r1_tarski('#skF_4', C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_10676])).
% 21.09/12.68  tff(c_10943, plain, (![C_1034]: (r2_hidden('#skF_5', k1_tops_1('#skF_3', C_1034)) | ~r1_tarski('#skF_4', C_1034) | ~m1_subset_1(C_1034, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_10680])).
% 21.09/12.68  tff(c_10976, plain, (![A_1035]: (r2_hidden('#skF_5', k1_tops_1('#skF_3', A_1035)) | ~r1_tarski('#skF_4', A_1035) | ~r1_tarski(A_1035, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_10943])).
% 21.09/12.68  tff(c_10980, plain, (![A_1035]: (m1_connsp_2(A_1035, '#skF_3', '#skF_5') | ~m1_subset_1(A_1035, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_4', A_1035) | ~r1_tarski(A_1035, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10976, c_40])).
% 21.09/12.68  tff(c_10992, plain, (![A_1035]: (m1_connsp_2(A_1035, '#skF_3', '#skF_5') | ~m1_subset_1(A_1035, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~r1_tarski('#skF_4', A_1035) | ~r1_tarski(A_1035, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_135, c_10980])).
% 21.09/12.68  tff(c_11002, plain, (![A_1036]: (m1_connsp_2(A_1036, '#skF_3', '#skF_5') | ~m1_subset_1(A_1036, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_4', A_1036) | ~r1_tarski(A_1036, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_10992])).
% 21.09/12.68  tff(c_11035, plain, (![A_1037]: (m1_connsp_2(A_1037, '#skF_3', '#skF_5') | ~r1_tarski('#skF_4', A_1037) | ~r1_tarski(A_1037, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_11002])).
% 21.09/12.68  tff(c_11065, plain, (m1_connsp_2(u1_struct_0('#skF_3'), '#skF_3', '#skF_5') | ~r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_11035])).
% 21.09/12.68  tff(c_11079, plain, (m1_connsp_2(u1_struct_0('#skF_3'), '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_11065])).
% 21.09/12.68  tff(c_832, plain, (![B_220, A_221, A_14]: (r2_hidden(B_220, k1_tops_1(A_221, A_14)) | ~m1_connsp_2(A_14, A_221, B_220) | ~m1_subset_1(B_220, u1_struct_0(A_221)) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221) | ~r1_tarski(A_14, u1_struct_0(A_221)))), inference(resolution, [status(thm)], [c_18, c_809])).
% 21.09/12.68  tff(c_350, plain, (![A_155, B_156, C_157]: (v3_pre_topc('#skF_2'(A_155, B_156, C_157), A_155) | ~r2_hidden(B_156, k1_tops_1(A_155, C_157)) | ~m1_subset_1(C_157, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.09/12.68  tff(c_365, plain, (![A_155, B_156, A_14]: (v3_pre_topc('#skF_2'(A_155, B_156, A_14), A_155) | ~r2_hidden(B_156, k1_tops_1(A_155, A_14)) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | ~r1_tarski(A_14, u1_struct_0(A_155)))), inference(resolution, [status(thm)], [c_18, c_350])).
% 21.09/12.68  tff(c_30, plain, (![A_29, B_36, C_37]: (r1_tarski('#skF_2'(A_29, B_36, C_37), C_37) | ~r2_hidden(B_36, k1_tops_1(A_29, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.09/12.68  tff(c_10984, plain, (![A_1035]: (r1_tarski('#skF_2'('#skF_3', '#skF_5', A_1035), A_1035) | ~m1_subset_1(A_1035, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski('#skF_4', A_1035) | ~r1_tarski(A_1035, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10976, c_30])).
% 21.09/12.68  tff(c_11848, plain, (![A_1099]: (r1_tarski('#skF_2'('#skF_3', '#skF_5', A_1099), A_1099) | ~m1_subset_1(A_1099, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_4', A_1099) | ~r1_tarski(A_1099, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_10984])).
% 21.09/12.68  tff(c_11875, plain, (![A_1100]: (r1_tarski('#skF_2'('#skF_3', '#skF_5', A_1100), A_1100) | ~r1_tarski('#skF_4', A_1100) | ~r1_tarski(A_1100, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_11848])).
% 21.09/12.68  tff(c_10742, plain, (![B_1021, A_1022, C_1023]: (m1_connsp_2(B_1021, A_1022, C_1023) | ~r2_hidden(C_1023, B_1021) | ~v3_pre_topc(B_1021, A_1022) | ~m1_subset_1(C_1023, u1_struct_0(A_1022)) | ~m1_subset_1(B_1021, k1_zfmisc_1(u1_struct_0(A_1022))) | ~l1_pre_topc(A_1022) | ~v2_pre_topc(A_1022) | v2_struct_0(A_1022))), inference(cnfTransformation, [status(thm)], [f_156])).
% 21.09/12.68  tff(c_10750, plain, (![B_1021]: (m1_connsp_2(B_1021, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_1021) | ~v3_pre_topc(B_1021, '#skF_3') | ~m1_subset_1(B_1021, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_135, c_10742])).
% 21.09/12.68  tff(c_10757, plain, (![B_1021]: (m1_connsp_2(B_1021, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_1021) | ~v3_pre_topc(B_1021, '#skF_3') | ~m1_subset_1(B_1021, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_10750])).
% 21.09/12.68  tff(c_10794, plain, (![B_1026]: (m1_connsp_2(B_1026, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_1026) | ~v3_pre_topc(B_1026, '#skF_3') | ~m1_subset_1(B_1026, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_10757])).
% 21.09/12.68  tff(c_10823, plain, (![A_14]: (m1_connsp_2(A_14, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', A_14) | ~v3_pre_topc(A_14, '#skF_3') | ~r1_tarski(A_14, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_10794])).
% 21.09/12.68  tff(c_11900, plain, (m1_connsp_2('#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3'))) | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')), '#skF_3') | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')) | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_11875, c_10823])).
% 21.09/12.68  tff(c_11948, plain, (m1_connsp_2('#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3'))) | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92, c_11900])).
% 21.09/12.68  tff(c_12371, plain, (~v3_pre_topc('#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_11948])).
% 21.09/12.68  tff(c_12378, plain, (~r2_hidden('#skF_5', k1_tops_1('#skF_3', u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_365, c_12371])).
% 21.09/12.68  tff(c_12381, plain, (~r2_hidden('#skF_5', k1_tops_1('#skF_3', u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50, c_48, c_12378])).
% 21.09/12.68  tff(c_12384, plain, (~m1_connsp_2(u1_struct_0('#skF_3'), '#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_832, c_12381])).
% 21.09/12.68  tff(c_12393, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50, c_48, c_135, c_11079, c_12384])).
% 21.09/12.68  tff(c_12395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_12393])).
% 21.09/12.69  tff(c_12397, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_11948])).
% 21.09/12.69  tff(c_34, plain, (![A_29, B_36, C_37]: (m1_subset_1('#skF_2'(A_29, B_36, C_37), k1_zfmisc_1(u1_struct_0(A_29))) | ~r2_hidden(B_36, k1_tops_1(A_29, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.09/12.69  tff(c_38, plain, (![B_49, D_55, C_53, A_41]: (k1_tops_1(B_49, D_55)=D_55 | ~v3_pre_topc(D_55, B_49) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0(B_49))) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(B_49) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_120])).
% 21.09/12.69  tff(c_586, plain, (![C_204, A_205]: (~m1_subset_1(C_204, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205))), inference(splitLeft, [status(thm)], [c_38])).
% 21.09/12.69  tff(c_604, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_586])).
% 21.09/12.69  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_604])).
% 21.09/12.69  tff(c_616, plain, (![B_206, D_207]: (k1_tops_1(B_206, D_207)=D_207 | ~v3_pre_topc(D_207, B_206) | ~m1_subset_1(D_207, k1_zfmisc_1(u1_struct_0(B_206))) | ~l1_pre_topc(B_206))), inference(splitRight, [status(thm)], [c_38])).
% 21.09/12.69  tff(c_639, plain, (![A_29, B_36, C_37]: (k1_tops_1(A_29, '#skF_2'(A_29, B_36, C_37))='#skF_2'(A_29, B_36, C_37) | ~v3_pre_topc('#skF_2'(A_29, B_36, C_37), A_29) | ~r2_hidden(B_36, k1_tops_1(A_29, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(resolution, [status(thm)], [c_34, c_616])).
% 21.09/12.69  tff(c_12399, plain, (k1_tops_1('#skF_3', '#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')))='#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_5', k1_tops_1('#skF_3', u1_struct_0('#skF_3'))) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12397, c_639])).
% 21.09/12.69  tff(c_12402, plain, (k1_tops_1('#skF_3', '#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')))='#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_5', k1_tops_1('#skF_3', u1_struct_0('#skF_3'))) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_12399])).
% 21.09/12.69  tff(c_14963, plain, (~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_12402])).
% 21.09/12.69  tff(c_14967, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_14963])).
% 21.09/12.69  tff(c_14971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14967])).
% 21.09/12.69  tff(c_14973, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_12402])).
% 21.09/12.69  tff(c_20, plain, (![A_16, C_18, B_17]: (m1_subset_1(A_16, C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(C_18)) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 21.09/12.69  tff(c_15105, plain, (![A_16]: (m1_subset_1(A_16, u1_struct_0('#skF_3')) | ~r2_hidden(A_16, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14973, c_20])).
% 21.09/12.69  tff(c_18784, plain, (![A_1530, C_1531]: (m1_subset_1('#skF_1'(A_1530, '#skF_4', C_1531), u1_struct_0('#skF_3')) | r1_tarski('#skF_4', C_1531) | ~m1_subset_1(C_1531, k1_zfmisc_1(A_1530)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1530)) | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18753, c_15105])).
% 21.09/12.69  tff(c_18848, plain, (![A_1530, C_1531]: (m1_subset_1('#skF_1'(A_1530, '#skF_4', C_1531), u1_struct_0('#skF_3')) | r1_tarski('#skF_4', C_1531) | ~m1_subset_1(C_1531, k1_zfmisc_1(A_1530)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1530)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18784])).
% 21.09/12.69  tff(c_20952, plain, (![B_1618, A_1619]: (r1_tarski(B_1618, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_1619)) | ~m1_subset_1(B_1618, k1_zfmisc_1(A_1619)) | ~m1_connsp_2('#skF_4', '#skF_3', '#skF_1'(A_1619, B_1618, k1_tops_1('#skF_3', '#skF_4'))) | ~m1_subset_1('#skF_1'(A_1619, B_1618, k1_tops_1('#skF_3', '#skF_4')), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_837, c_10])).
% 21.09/12.69  tff(c_20960, plain, (![A_1530]: (~m1_connsp_2('#skF_4', '#skF_3', '#skF_1'(A_1530, '#skF_4', k1_tops_1('#skF_3', '#skF_4'))) | r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_1530)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1530)))), inference(resolution, [status(thm)], [c_18848, c_20952])).
% 21.09/12.69  tff(c_20991, plain, (![A_1530]: (~m1_connsp_2('#skF_4', '#skF_3', '#skF_1'(A_1530, '#skF_4', k1_tops_1('#skF_3', '#skF_4'))) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_1530)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1530)))), inference(negUnitSimplification, [status(thm)], [c_198, c_198, c_20960])).
% 21.09/12.69  tff(c_43554, plain, (![A_2504]: (~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_2504)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2504)) | ~r2_hidden('#skF_1'(A_2504, '#skF_4', k1_tops_1('#skF_3', '#skF_4')), '#skF_4'))), inference(resolution, [status(thm)], [c_40005, c_20991])).
% 21.09/12.69  tff(c_43578, plain, (![A_1556]: (r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_1556)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1556)) | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_19494, c_43554])).
% 21.09/12.69  tff(c_43605, plain, (![A_1556]: (r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_1556)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1556)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_43578])).
% 21.09/12.69  tff(c_43615, plain, (![A_2505]: (~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_2505)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2505)))), inference(negUnitSimplification, [status(thm)], [c_198, c_43605])).
% 21.09/12.69  tff(c_43762, plain, (![B_2510]: (~m1_subset_1('#skF_4', k1_zfmisc_1(B_2510)) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2510))), inference(resolution, [status(thm)], [c_18, c_43615])).
% 21.09/12.69  tff(c_43809, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20525, c_43762])).
% 21.09/12.69  tff(c_43852, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_6, c_43809])).
% 21.09/12.69  tff(c_43866, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_43852])).
% 21.09/12.69  tff(c_43870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_43866])).
% 21.09/12.69  tff(c_43871, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_169])).
% 21.09/12.69  tff(c_44201, plain, (![A_2582, B_2583, C_2584]: (r1_tarski(k1_tops_1(A_2582, B_2583), k1_tops_1(A_2582, C_2584)) | ~r1_tarski(B_2583, C_2584) | ~m1_subset_1(C_2584, k1_zfmisc_1(u1_struct_0(A_2582))) | ~m1_subset_1(B_2583, k1_zfmisc_1(u1_struct_0(A_2582))) | ~l1_pre_topc(A_2582))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.09/12.69  tff(c_44212, plain, (![C_2584]: (r1_tarski('#skF_4', k1_tops_1('#skF_3', C_2584)) | ~r1_tarski('#skF_4', C_2584) | ~m1_subset_1(C_2584, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_43871, c_44201])).
% 21.09/12.69  tff(c_44223, plain, (![C_2585]: (r1_tarski('#skF_4', k1_tops_1('#skF_3', C_2585)) | ~r1_tarski('#skF_4', C_2585) | ~m1_subset_1(C_2585, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44212])).
% 21.09/12.69  tff(c_44251, plain, (![A_2586]: (r1_tarski('#skF_4', k1_tops_1('#skF_3', A_2586)) | ~r1_tarski('#skF_4', A_2586) | ~r1_tarski(A_2586, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_44223])).
% 21.09/12.69  tff(c_44264, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_3', u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_44251])).
% 21.09/12.69  tff(c_44273, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_3', u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_44264])).
% 21.09/12.69  tff(c_137, plain, (![C_109, A_110, B_111]: (r2_hidden(C_109, A_110) | ~r2_hidden(C_109, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 21.09/12.69  tff(c_141, plain, (![A_112]: (r2_hidden('#skF_5', A_112) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_112)))), inference(resolution, [status(thm)], [c_93, c_137])).
% 21.09/12.69  tff(c_170, plain, (![B_115]: (r2_hidden('#skF_5', B_115) | ~r1_tarski('#skF_4', B_115))), inference(resolution, [status(thm)], [c_18, c_141])).
% 21.09/12.69  tff(c_43893, plain, (![A_2513, B_2514]: (r2_hidden('#skF_5', A_2513) | ~m1_subset_1(B_2514, k1_zfmisc_1(A_2513)) | ~r1_tarski('#skF_4', B_2514))), inference(resolution, [status(thm)], [c_170, c_8])).
% 21.09/12.69  tff(c_43900, plain, (![B_15, A_14]: (r2_hidden('#skF_5', B_15) | ~r1_tarski('#skF_4', A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_18, c_43893])).
% 21.09/12.69  tff(c_44295, plain, (![B_2587]: (r2_hidden('#skF_5', B_2587) | ~r1_tarski(k1_tops_1('#skF_3', u1_struct_0('#skF_3')), B_2587))), inference(resolution, [status(thm)], [c_44273, c_43900])).
% 21.09/12.69  tff(c_44314, plain, (r2_hidden('#skF_5', k1_tops_1('#skF_3', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_44295])).
% 21.09/12.69  tff(c_28, plain, (![B_36, A_29, C_37]: (r2_hidden(B_36, '#skF_2'(A_29, B_36, C_37)) | ~r2_hidden(B_36, k1_tops_1(A_29, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.09/12.69  tff(c_44316, plain, (r2_hidden('#skF_5', '#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3'))) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44314, c_28])).
% 21.09/12.69  tff(c_44325, plain, (r2_hidden('#skF_5', '#skF_2'('#skF_3', '#skF_5', u1_struct_0('#skF_3'))) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44316])).
% 21.09/12.69  tff(c_44471, plain, (~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_44325])).
% 21.09/12.69  tff(c_44474, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_44471])).
% 21.09/12.69  tff(c_44478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_44474])).
% 21.09/12.69  tff(c_44480, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_44325])).
% 21.09/12.69  tff(c_36, plain, (![C_53, A_41, D_55, B_49]: (v3_pre_topc(C_53, A_41) | k1_tops_1(A_41, C_53)!=C_53 | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0(B_49))) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(B_49) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_120])).
% 21.09/12.69  tff(c_44639, plain, (![D_2599, B_2600]: (~m1_subset_1(D_2599, k1_zfmisc_1(u1_struct_0(B_2600))) | ~l1_pre_topc(B_2600))), inference(splitLeft, [status(thm)], [c_36])).
% 21.09/12.69  tff(c_44642, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44480, c_44639])).
% 21.09/12.69  tff(c_44660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44642])).
% 21.09/12.69  tff(c_44716, plain, (![C_2606, A_2607]: (v3_pre_topc(C_2606, A_2607) | k1_tops_1(A_2607, C_2606)!=C_2606 | ~m1_subset_1(C_2606, k1_zfmisc_1(u1_struct_0(A_2607))) | ~l1_pre_topc(A_2607) | ~v2_pre_topc(A_2607))), inference(splitRight, [status(thm)], [c_36])).
% 21.09/12.69  tff(c_44736, plain, (v3_pre_topc('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_44716])).
% 21.09/12.69  tff(c_44749, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_43871, c_44736])).
% 21.09/12.69  tff(c_44751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_44749])).
% 21.09/12.69  tff(c_44753, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 21.09/12.69  tff(c_54, plain, (![D_90]: (~r1_tarski(D_90, '#skF_4') | ~m1_connsp_2(D_90, '#skF_3', '#skF_5') | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.69  tff(c_44851, plain, (![D_2630]: (~r1_tarski(D_2630, '#skF_4') | ~m1_connsp_2(D_2630, '#skF_3', '#skF_5') | ~m1_subset_1(D_2630, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44753, c_54])).
% 21.09/12.69  tff(c_44858, plain, (~r1_tarski('#skF_4', '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_44851])).
% 21.09/12.69  tff(c_44862, plain, (~m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_44858])).
% 21.09/12.69  tff(c_44752, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 21.09/12.69  tff(c_58, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 21.09/12.69  tff(c_44755, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44753, c_58])).
% 21.09/12.69  tff(c_45226, plain, (![C_2706, A_2707]: (~m1_subset_1(C_2706, k1_zfmisc_1(u1_struct_0(A_2707))) | ~l1_pre_topc(A_2707) | ~v2_pre_topc(A_2707))), inference(splitLeft, [status(thm)], [c_38])).
% 21.09/12.69  tff(c_45241, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_45226])).
% 21.09/12.69  tff(c_45248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_45241])).
% 21.09/12.69  tff(c_45250, plain, (![B_2708, D_2709]: (k1_tops_1(B_2708, D_2709)=D_2709 | ~v3_pre_topc(D_2709, B_2708) | ~m1_subset_1(D_2709, k1_zfmisc_1(u1_struct_0(B_2708))) | ~l1_pre_topc(B_2708))), inference(splitRight, [status(thm)], [c_38])).
% 21.09/12.69  tff(c_45268, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_45250])).
% 21.09/12.69  tff(c_45275, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44753, c_45268])).
% 21.09/12.69  tff(c_44822, plain, (![A_2626, B_2627]: (r1_tarski(k1_tops_1(A_2626, B_2627), B_2627) | ~m1_subset_1(B_2627, k1_zfmisc_1(u1_struct_0(A_2626))) | ~l1_pre_topc(A_2626))), inference(cnfTransformation, [status(thm)], [f_69])).
% 21.09/12.69  tff(c_44827, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_44822])).
% 21.09/12.69  tff(c_44831, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44827])).
% 21.09/12.69  tff(c_44834, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44831, c_2])).
% 21.09/12.69  tff(c_44876, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_44834])).
% 21.09/12.69  tff(c_45277, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45275, c_44876])).
% 21.09/12.69  tff(c_45281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_45277])).
% 21.09/12.69  tff(c_45282, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_44834])).
% 21.09/12.69  tff(c_46277, plain, (![C_2807, A_2808, B_2809]: (m1_connsp_2(C_2807, A_2808, B_2809) | ~r2_hidden(B_2809, k1_tops_1(A_2808, C_2807)) | ~m1_subset_1(C_2807, k1_zfmisc_1(u1_struct_0(A_2808))) | ~m1_subset_1(B_2809, u1_struct_0(A_2808)) | ~l1_pre_topc(A_2808) | ~v2_pre_topc(A_2808) | v2_struct_0(A_2808))), inference(cnfTransformation, [status(thm)], [f_137])).
% 21.09/12.69  tff(c_46286, plain, (![B_2809]: (m1_connsp_2('#skF_4', '#skF_3', B_2809) | ~r2_hidden(B_2809, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_2809, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_45282, c_46277])).
% 21.09/12.69  tff(c_46300, plain, (![B_2809]: (m1_connsp_2('#skF_4', '#skF_3', B_2809) | ~r2_hidden(B_2809, '#skF_4') | ~m1_subset_1(B_2809, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_46286])).
% 21.09/12.69  tff(c_46303, plain, (![B_2810]: (m1_connsp_2('#skF_4', '#skF_3', B_2810) | ~r2_hidden(B_2810, '#skF_4') | ~m1_subset_1(B_2810, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_46300])).
% 21.09/12.69  tff(c_46313, plain, (m1_connsp_2('#skF_4', '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44755, c_46303])).
% 21.09/12.69  tff(c_46318, plain, (m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44752, c_46313])).
% 21.09/12.69  tff(c_46320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44862, c_46318])).
% 21.09/12.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.09/12.69  
% 21.09/12.69  Inference rules
% 21.09/12.69  ----------------------
% 21.09/12.69  #Ref     : 0
% 21.09/12.69  #Sup     : 9876
% 21.09/12.69  #Fact    : 0
% 21.09/12.69  #Define  : 0
% 21.09/12.69  #Split   : 53
% 21.09/12.69  #Chain   : 0
% 21.09/12.69  #Close   : 0
% 21.09/12.69  
% 21.09/12.69  Ordering : KBO
% 21.09/12.69  
% 21.09/12.69  Simplification rules
% 21.09/12.69  ----------------------
% 21.09/12.69  #Subsume      : 3425
% 21.09/12.69  #Demod        : 10093
% 21.09/12.69  #Tautology    : 1107
% 21.09/12.69  #SimpNegUnit  : 769
% 21.09/12.69  #BackRed      : 5
% 21.09/12.69  
% 21.09/12.69  #Partial instantiations: 0
% 21.09/12.69  #Strategies tried      : 1
% 21.09/12.69  
% 21.09/12.69  Timing (in seconds)
% 21.09/12.69  ----------------------
% 21.09/12.69  Preprocessing        : 0.34
% 21.09/12.69  Parsing              : 0.18
% 21.09/12.69  CNF conversion       : 0.03
% 21.09/12.69  Main loop            : 11.45
% 21.09/12.69  Inferencing          : 2.34
% 21.09/12.69  Reduction            : 2.91
% 21.09/12.69  Demodulation         : 2.04
% 21.09/12.69  BG Simplification    : 0.17
% 21.09/12.69  Subsumption          : 5.35
% 21.09/12.69  Abstraction          : 0.31
% 21.09/12.69  MUC search           : 0.00
% 21.09/12.69  Cooper               : 0.00
% 21.09/12.69  Total                : 11.87
% 21.09/12.69  Index Insertion      : 0.00
% 21.09/12.69  Index Deletion       : 0.00
% 21.09/12.69  Index Matching       : 0.00
% 21.09/12.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
