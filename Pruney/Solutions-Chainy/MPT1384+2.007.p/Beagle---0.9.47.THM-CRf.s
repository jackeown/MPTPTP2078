%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:14 EST 2020

% Result     : Theorem 51.70s
% Output     : CNFRefutation 51.70s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 226 expanded)
%              Number of leaves         :   28 (  88 expanded)
%              Depth                    :   21
%              Number of atoms          :  306 ( 896 expanded)
%              Number of equality atoms :    4 (  13 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_152,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_125,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_75,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_145,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(k1_tops_1(A_89,B_90),B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_150,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_145])).

tff(c_154,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_150])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_154,c_8])).

tff(c_158,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_80,C_81,B_82] :
      ( m1_subset_1(A_80,C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,(
    ! [A_80] :
      ( m1_subset_1(A_80,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_80,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_109])).

tff(c_56,plain,(
    ! [C_64] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | r1_tarski('#skF_5'(C_64),'#skF_3')
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_159,plain,(
    ! [C_64] :
      ( r1_tarski('#skF_5'(C_64),'#skF_3')
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_56])).

tff(c_105,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_239,plain,(
    ! [A_102,B_103,B_104] :
      ( r2_hidden('#skF_1'(A_102,B_103),B_104)
      | ~ r1_tarski(A_102,B_104)
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_283,plain,(
    ! [A_115,B_116,B_117,B_118] :
      ( r2_hidden('#skF_1'(A_115,B_116),B_117)
      | ~ r1_tarski(B_118,B_117)
      | ~ r1_tarski(A_115,B_118)
      | r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_239,c_2])).

tff(c_83887,plain,(
    ! [A_1827,B_1828,C_1829] :
      ( r2_hidden('#skF_1'(A_1827,B_1828),'#skF_3')
      | ~ r1_tarski(A_1827,'#skF_5'(C_1829))
      | r1_tarski(A_1827,B_1828)
      | ~ r2_hidden(C_1829,'#skF_3')
      | ~ m1_subset_1(C_1829,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_159,c_283])).

tff(c_84142,plain,(
    ! [C_1832,B_1833] :
      ( r2_hidden('#skF_1'('#skF_5'(C_1832),B_1833),'#skF_3')
      | r1_tarski('#skF_5'(C_1832),B_1833)
      | ~ r2_hidden(C_1832,'#skF_3')
      | ~ m1_subset_1(C_1832,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_83887])).

tff(c_124043,plain,(
    ! [C_2412,B_2413,B_2414] :
      ( r2_hidden('#skF_1'('#skF_5'(C_2412),B_2413),B_2414)
      | ~ r1_tarski('#skF_3',B_2414)
      | r1_tarski('#skF_5'(C_2412),B_2413)
      | ~ r2_hidden(C_2412,'#skF_3')
      | ~ m1_subset_1(C_2412,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_84142,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124162,plain,(
    ! [B_2414,C_2412] :
      ( ~ r1_tarski('#skF_3',B_2414)
      | r1_tarski('#skF_5'(C_2412),B_2414)
      | ~ r2_hidden(C_2412,'#skF_3')
      | ~ m1_subset_1(C_2412,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_124043,c_4])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_72,plain,(
    ! [C_64] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | m1_subset_1('#skF_5'(C_64),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_514,plain,(
    ! [C_64] :
      ( m1_subset_1('#skF_5'(C_64),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_72])).

tff(c_64,plain,(
    ! [C_64] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | m1_connsp_2('#skF_5'(C_64),'#skF_2',C_64)
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_281,plain,(
    ! [C_64] :
      ( m1_connsp_2('#skF_5'(C_64),'#skF_2',C_64)
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_64])).

tff(c_24,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_tarski(k1_tops_1(A_18,B_22),k1_tops_1(A_18,C_24))
      | ~ r1_tarski(B_22,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1058,plain,(
    ! [B_209,A_210,C_211] :
      ( r2_hidden(B_209,k1_tops_1(A_210,C_211))
      | ~ m1_connsp_2(C_211,A_210,B_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ m1_subset_1(B_209,u1_struct_0(A_210))
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1063,plain,(
    ! [B_209,C_64] :
      ( r2_hidden(B_209,k1_tops_1('#skF_2','#skF_5'(C_64)))
      | ~ m1_connsp_2('#skF_5'(C_64),'#skF_2',B_209)
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_514,c_1058])).

tff(c_1075,plain,(
    ! [B_209,C_64] :
      ( r2_hidden(B_209,k1_tops_1('#skF_2','#skF_5'(C_64)))
      | ~ m1_connsp_2('#skF_5'(C_64),'#skF_2',B_209)
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1063])).

tff(c_1170,plain,(
    ! [B_216,C_217] :
      ( r2_hidden(B_216,k1_tops_1('#skF_2','#skF_5'(C_217)))
      | ~ m1_connsp_2('#skF_5'(C_217),'#skF_2',B_216)
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_217,'#skF_3')
      | ~ m1_subset_1(C_217,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1075])).

tff(c_77129,plain,(
    ! [B_1657,B_1658,C_1659] :
      ( r2_hidden(B_1657,B_1658)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'(C_1659)),B_1658)
      | ~ m1_connsp_2('#skF_5'(C_1659),'#skF_2',B_1657)
      | ~ m1_subset_1(B_1657,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_1659,'#skF_3')
      | ~ m1_subset_1(C_1659,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1170,c_2])).

tff(c_77152,plain,(
    ! [B_1657,C_24,C_1659] :
      ( r2_hidden(B_1657,k1_tops_1('#skF_2',C_24))
      | ~ m1_connsp_2('#skF_5'(C_1659),'#skF_2',B_1657)
      | ~ m1_subset_1(B_1657,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_1659,'#skF_3')
      | ~ m1_subset_1(C_1659,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5'(C_1659),C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5'(C_1659),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_77129])).

tff(c_121408,plain,(
    ! [B_2379,C_2380,C_2381] :
      ( r2_hidden(B_2379,k1_tops_1('#skF_2',C_2380))
      | ~ m1_connsp_2('#skF_5'(C_2381),'#skF_2',B_2379)
      | ~ m1_subset_1(B_2379,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_2381,'#skF_3')
      | ~ m1_subset_1(C_2381,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5'(C_2381),C_2380)
      | ~ m1_subset_1(C_2380,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5'(C_2381),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_77152])).

tff(c_175187,plain,(
    ! [C_2880,C_2881] :
      ( r2_hidden(C_2880,k1_tops_1('#skF_2',C_2881))
      | ~ r1_tarski('#skF_5'(C_2880),C_2881)
      | ~ m1_subset_1(C_2881,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5'(C_2880),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_2880,'#skF_3')
      | ~ m1_subset_1(C_2880,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_281,c_121408])).

tff(c_175672,plain,(
    ! [C_2893] :
      ( r2_hidden(C_2893,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_5'(C_2893),'#skF_3')
      | ~ m1_subset_1('#skF_5'(C_2893),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_2893,'#skF_3')
      | ~ m1_subset_1(C_2893,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_175187])).

tff(c_175705,plain,(
    ! [C_2894] :
      ( r2_hidden(C_2894,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_5'(C_2894),'#skF_3')
      | ~ r2_hidden(C_2894,'#skF_3')
      | ~ m1_subset_1(C_2894,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_514,c_175672])).

tff(c_26,plain,(
    ! [C_31,A_25,B_29] :
      ( m1_connsp_2(C_31,A_25,B_29)
      | ~ r2_hidden(B_29,k1_tops_1(A_25,C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_29,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_175741,plain,(
    ! [C_2894] :
      ( m1_connsp_2('#skF_3','#skF_2',C_2894)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_5'(C_2894),'#skF_3')
      | ~ r2_hidden(C_2894,'#skF_3')
      | ~ m1_subset_1(C_2894,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_175705,c_26])).

tff(c_175787,plain,(
    ! [C_2894] :
      ( m1_connsp_2('#skF_3','#skF_2',C_2894)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_5'(C_2894),'#skF_3')
      | ~ r2_hidden(C_2894,'#skF_3')
      | ~ m1_subset_1(C_2894,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_175741])).

tff(c_175792,plain,(
    ! [C_2895] :
      ( m1_connsp_2('#skF_3','#skF_2',C_2895)
      | ~ r1_tarski('#skF_5'(C_2895),'#skF_3')
      | ~ r2_hidden(C_2895,'#skF_3')
      | ~ m1_subset_1(C_2895,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_175787])).

tff(c_175799,plain,(
    ! [C_2412] :
      ( m1_connsp_2('#skF_3','#skF_2',C_2412)
      | ~ r1_tarski('#skF_3','#skF_3')
      | ~ r2_hidden(C_2412,'#skF_3')
      | ~ m1_subset_1(C_2412,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_124162,c_175792])).

tff(c_175814,plain,(
    ! [C_2896] :
      ( m1_connsp_2('#skF_3','#skF_2',C_2896)
      | ~ r2_hidden(C_2896,'#skF_3')
      | ~ m1_subset_1(C_2896,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_175799])).

tff(c_175964,plain,(
    ! [A_2897] :
      ( m1_connsp_2('#skF_3','#skF_2',A_2897)
      | ~ r2_hidden(A_2897,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_115,c_175814])).

tff(c_1071,plain,(
    ! [B_209] :
      ( r2_hidden(B_209,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_209)
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_1058])).

tff(c_1081,plain,(
    ! [B_209] :
      ( r2_hidden(B_209,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_209)
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1071])).

tff(c_1083,plain,(
    ! [B_212] :
      ( r2_hidden(B_212,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_212)
      | ~ m1_subset_1(B_212,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1081])).

tff(c_75655,plain,(
    ! [A_1625] :
      ( r1_tarski(A_1625,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2','#skF_1'(A_1625,k1_tops_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'(A_1625,k1_tops_1('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1083,c_4])).

tff(c_75699,plain,(
    ! [A_1625] :
      ( r1_tarski(A_1625,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2','#skF_1'(A_1625,k1_tops_1('#skF_2','#skF_3')))
      | ~ r2_hidden('#skF_1'(A_1625,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_115,c_75655])).

tff(c_176279,plain,(
    ! [A_2900] :
      ( r1_tarski(A_2900,k1_tops_1('#skF_2','#skF_3'))
      | ~ r2_hidden('#skF_1'(A_2900,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_175964,c_75699])).

tff(c_176375,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_176279])).

tff(c_176418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_158,c_176375])).

tff(c_176419,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_176459,plain,(
    ! [A_2905,B_2906] :
      ( v3_pre_topc(k1_tops_1(A_2905,B_2906),A_2905)
      | ~ m1_subset_1(B_2906,k1_zfmisc_1(u1_struct_0(A_2905)))
      | ~ l1_pre_topc(A_2905)
      | ~ v2_pre_topc(A_2905) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_176464,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_176459])).

tff(c_176468,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_176419,c_176464])).

tff(c_176470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_176468])).

tff(c_176472,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_63] :
      ( ~ r1_tarski(D_63,'#skF_3')
      | ~ m1_connsp_2(D_63,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_176687,plain,(
    ! [D_2958] :
      ( ~ r1_tarski(D_2958,'#skF_3')
      | ~ m1_connsp_2(D_2958,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_2958,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176472,c_42])).

tff(c_176698,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_176687])).

tff(c_176703,plain,(
    ~ m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_176698])).

tff(c_176471,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_176475,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176472,c_46])).

tff(c_177845,plain,(
    ! [B_3078,A_3079,C_3080] :
      ( m1_connsp_2(B_3078,A_3079,C_3080)
      | ~ r2_hidden(C_3080,B_3078)
      | ~ v3_pre_topc(B_3078,A_3079)
      | ~ m1_subset_1(C_3080,u1_struct_0(A_3079))
      | ~ m1_subset_1(B_3078,k1_zfmisc_1(u1_struct_0(A_3079)))
      | ~ l1_pre_topc(A_3079)
      | ~ v2_pre_topc(A_3079)
      | v2_struct_0(A_3079) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_177864,plain,(
    ! [B_3078] :
      ( m1_connsp_2(B_3078,'#skF_2','#skF_4')
      | ~ r2_hidden('#skF_4',B_3078)
      | ~ v3_pre_topc(B_3078,'#skF_2')
      | ~ m1_subset_1(B_3078,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_176475,c_177845])).

tff(c_177886,plain,(
    ! [B_3078] :
      ( m1_connsp_2(B_3078,'#skF_2','#skF_4')
      | ~ r2_hidden('#skF_4',B_3078)
      | ~ v3_pre_topc(B_3078,'#skF_2')
      | ~ m1_subset_1(B_3078,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_177864])).

tff(c_177888,plain,(
    ! [B_3081] :
      ( m1_connsp_2(B_3081,'#skF_2','#skF_4')
      | ~ r2_hidden('#skF_4',B_3081)
      | ~ v3_pre_topc(B_3081,'#skF_2')
      | ~ m1_subset_1(B_3081,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_177886])).

tff(c_177907,plain,
    ( m1_connsp_2('#skF_3','#skF_2','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_177888])).

tff(c_177914,plain,(
    m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176472,c_176471,c_177907])).

tff(c_177916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176703,c_177914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 51.70/39.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.70/39.98  
% 51.70/39.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.70/39.98  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 51.70/39.98  
% 51.70/39.98  %Foreground sorts:
% 51.70/39.98  
% 51.70/39.98  
% 51.70/39.98  %Background operators:
% 51.70/39.98  
% 51.70/39.98  
% 51.70/39.98  %Foreground operators:
% 51.70/39.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 51.70/39.98  tff('#skF_5', type, '#skF_5': $i > $i).
% 51.70/39.98  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 51.70/39.98  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 51.70/39.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 51.70/39.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 51.70/39.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 51.70/39.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 51.70/39.98  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 51.70/39.98  tff('#skF_2', type, '#skF_2': $i).
% 51.70/39.98  tff('#skF_3', type, '#skF_3': $i).
% 51.70/39.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 51.70/39.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 51.70/39.98  tff('#skF_4', type, '#skF_4': $i).
% 51.70/39.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 51.70/39.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 51.70/39.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 51.70/39.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 51.70/39.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 51.70/39.98  
% 51.70/40.00  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 51.70/40.00  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 51.70/40.00  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 51.70/40.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 51.70/40.00  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 51.70/40.00  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 51.70/40.00  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 51.70/40.00  tff(f_56, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 51.70/40.00  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 51.70/40.00  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 51.70/40.00  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_44, plain, (r2_hidden('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_75, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 51.70/40.00  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_145, plain, (![A_89, B_90]: (r1_tarski(k1_tops_1(A_89, B_90), B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_63])).
% 51.70/40.00  tff(c_150, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_145])).
% 51.70/40.00  tff(c_154, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_150])).
% 51.70/40.00  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 51.70/40.00  tff(c_157, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_154, c_8])).
% 51.70/40.00  tff(c_158, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_157])).
% 51.70/40.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 51.70/40.00  tff(c_109, plain, (![A_80, C_81, B_82]: (m1_subset_1(A_80, C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_48])).
% 51.70/40.00  tff(c_115, plain, (![A_80]: (m1_subset_1(A_80, u1_struct_0('#skF_2')) | ~r2_hidden(A_80, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_109])).
% 51.70/40.00  tff(c_56, plain, (![C_64]: (v3_pre_topc('#skF_3', '#skF_2') | r1_tarski('#skF_5'(C_64), '#skF_3') | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_159, plain, (![C_64]: (r1_tarski('#skF_5'(C_64), '#skF_3') | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_75, c_56])).
% 51.70/40.00  tff(c_105, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 51.70/40.00  tff(c_239, plain, (![A_102, B_103, B_104]: (r2_hidden('#skF_1'(A_102, B_103), B_104) | ~r1_tarski(A_102, B_104) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_6, c_105])).
% 51.70/40.00  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 51.70/40.00  tff(c_283, plain, (![A_115, B_116, B_117, B_118]: (r2_hidden('#skF_1'(A_115, B_116), B_117) | ~r1_tarski(B_118, B_117) | ~r1_tarski(A_115, B_118) | r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_239, c_2])).
% 51.70/40.00  tff(c_83887, plain, (![A_1827, B_1828, C_1829]: (r2_hidden('#skF_1'(A_1827, B_1828), '#skF_3') | ~r1_tarski(A_1827, '#skF_5'(C_1829)) | r1_tarski(A_1827, B_1828) | ~r2_hidden(C_1829, '#skF_3') | ~m1_subset_1(C_1829, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_159, c_283])).
% 51.70/40.00  tff(c_84142, plain, (![C_1832, B_1833]: (r2_hidden('#skF_1'('#skF_5'(C_1832), B_1833), '#skF_3') | r1_tarski('#skF_5'(C_1832), B_1833) | ~r2_hidden(C_1832, '#skF_3') | ~m1_subset_1(C_1832, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_83887])).
% 51.70/40.00  tff(c_124043, plain, (![C_2412, B_2413, B_2414]: (r2_hidden('#skF_1'('#skF_5'(C_2412), B_2413), B_2414) | ~r1_tarski('#skF_3', B_2414) | r1_tarski('#skF_5'(C_2412), B_2413) | ~r2_hidden(C_2412, '#skF_3') | ~m1_subset_1(C_2412, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_84142, c_2])).
% 51.70/40.00  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 51.70/40.00  tff(c_124162, plain, (![B_2414, C_2412]: (~r1_tarski('#skF_3', B_2414) | r1_tarski('#skF_5'(C_2412), B_2414) | ~r2_hidden(C_2412, '#skF_3') | ~m1_subset_1(C_2412, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_124043, c_4])).
% 51.70/40.00  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_72, plain, (![C_64]: (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1('#skF_5'(C_64), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_514, plain, (![C_64]: (m1_subset_1('#skF_5'(C_64), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_75, c_72])).
% 51.70/40.00  tff(c_64, plain, (![C_64]: (v3_pre_topc('#skF_3', '#skF_2') | m1_connsp_2('#skF_5'(C_64), '#skF_2', C_64) | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_281, plain, (![C_64]: (m1_connsp_2('#skF_5'(C_64), '#skF_2', C_64) | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_75, c_64])).
% 51.70/40.00  tff(c_24, plain, (![A_18, B_22, C_24]: (r1_tarski(k1_tops_1(A_18, B_22), k1_tops_1(A_18, C_24)) | ~r1_tarski(B_22, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 51.70/40.00  tff(c_1058, plain, (![B_209, A_210, C_211]: (r2_hidden(B_209, k1_tops_1(A_210, C_211)) | ~m1_connsp_2(C_211, A_210, B_209) | ~m1_subset_1(C_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~m1_subset_1(B_209, u1_struct_0(A_210)) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_92])).
% 51.70/40.00  tff(c_1063, plain, (![B_209, C_64]: (r2_hidden(B_209, k1_tops_1('#skF_2', '#skF_5'(C_64))) | ~m1_connsp_2('#skF_5'(C_64), '#skF_2', B_209) | ~m1_subset_1(B_209, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_514, c_1058])).
% 51.70/40.00  tff(c_1075, plain, (![B_209, C_64]: (r2_hidden(B_209, k1_tops_1('#skF_2', '#skF_5'(C_64))) | ~m1_connsp_2('#skF_5'(C_64), '#skF_2', B_209) | ~m1_subset_1(B_209, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1063])).
% 51.70/40.00  tff(c_1170, plain, (![B_216, C_217]: (r2_hidden(B_216, k1_tops_1('#skF_2', '#skF_5'(C_217))) | ~m1_connsp_2('#skF_5'(C_217), '#skF_2', B_216) | ~m1_subset_1(B_216, u1_struct_0('#skF_2')) | ~r2_hidden(C_217, '#skF_3') | ~m1_subset_1(C_217, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1075])).
% 51.70/40.00  tff(c_77129, plain, (![B_1657, B_1658, C_1659]: (r2_hidden(B_1657, B_1658) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'(C_1659)), B_1658) | ~m1_connsp_2('#skF_5'(C_1659), '#skF_2', B_1657) | ~m1_subset_1(B_1657, u1_struct_0('#skF_2')) | ~r2_hidden(C_1659, '#skF_3') | ~m1_subset_1(C_1659, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1170, c_2])).
% 51.70/40.00  tff(c_77152, plain, (![B_1657, C_24, C_1659]: (r2_hidden(B_1657, k1_tops_1('#skF_2', C_24)) | ~m1_connsp_2('#skF_5'(C_1659), '#skF_2', B_1657) | ~m1_subset_1(B_1657, u1_struct_0('#skF_2')) | ~r2_hidden(C_1659, '#skF_3') | ~m1_subset_1(C_1659, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5'(C_1659), C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5'(C_1659), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_77129])).
% 51.70/40.00  tff(c_121408, plain, (![B_2379, C_2380, C_2381]: (r2_hidden(B_2379, k1_tops_1('#skF_2', C_2380)) | ~m1_connsp_2('#skF_5'(C_2381), '#skF_2', B_2379) | ~m1_subset_1(B_2379, u1_struct_0('#skF_2')) | ~r2_hidden(C_2381, '#skF_3') | ~m1_subset_1(C_2381, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5'(C_2381), C_2380) | ~m1_subset_1(C_2380, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5'(C_2381), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_77152])).
% 51.70/40.00  tff(c_175187, plain, (![C_2880, C_2881]: (r2_hidden(C_2880, k1_tops_1('#skF_2', C_2881)) | ~r1_tarski('#skF_5'(C_2880), C_2881) | ~m1_subset_1(C_2881, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5'(C_2880), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_2880, '#skF_3') | ~m1_subset_1(C_2880, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_281, c_121408])).
% 51.70/40.00  tff(c_175672, plain, (![C_2893]: (r2_hidden(C_2893, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_5'(C_2893), '#skF_3') | ~m1_subset_1('#skF_5'(C_2893), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_2893, '#skF_3') | ~m1_subset_1(C_2893, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_175187])).
% 51.70/40.00  tff(c_175705, plain, (![C_2894]: (r2_hidden(C_2894, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_5'(C_2894), '#skF_3') | ~r2_hidden(C_2894, '#skF_3') | ~m1_subset_1(C_2894, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_514, c_175672])).
% 51.70/40.00  tff(c_26, plain, (![C_31, A_25, B_29]: (m1_connsp_2(C_31, A_25, B_29) | ~r2_hidden(B_29, k1_tops_1(A_25, C_31)) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_29, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 51.70/40.00  tff(c_175741, plain, (![C_2894]: (m1_connsp_2('#skF_3', '#skF_2', C_2894) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5'(C_2894), '#skF_3') | ~r2_hidden(C_2894, '#skF_3') | ~m1_subset_1(C_2894, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_175705, c_26])).
% 51.70/40.00  tff(c_175787, plain, (![C_2894]: (m1_connsp_2('#skF_3', '#skF_2', C_2894) | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5'(C_2894), '#skF_3') | ~r2_hidden(C_2894, '#skF_3') | ~m1_subset_1(C_2894, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_175741])).
% 51.70/40.00  tff(c_175792, plain, (![C_2895]: (m1_connsp_2('#skF_3', '#skF_2', C_2895) | ~r1_tarski('#skF_5'(C_2895), '#skF_3') | ~r2_hidden(C_2895, '#skF_3') | ~m1_subset_1(C_2895, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_175787])).
% 51.70/40.00  tff(c_175799, plain, (![C_2412]: (m1_connsp_2('#skF_3', '#skF_2', C_2412) | ~r1_tarski('#skF_3', '#skF_3') | ~r2_hidden(C_2412, '#skF_3') | ~m1_subset_1(C_2412, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_124162, c_175792])).
% 51.70/40.00  tff(c_175814, plain, (![C_2896]: (m1_connsp_2('#skF_3', '#skF_2', C_2896) | ~r2_hidden(C_2896, '#skF_3') | ~m1_subset_1(C_2896, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_175799])).
% 51.70/40.00  tff(c_175964, plain, (![A_2897]: (m1_connsp_2('#skF_3', '#skF_2', A_2897) | ~r2_hidden(A_2897, '#skF_3'))), inference(resolution, [status(thm)], [c_115, c_175814])).
% 51.70/40.00  tff(c_1071, plain, (![B_209]: (r2_hidden(B_209, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_209) | ~m1_subset_1(B_209, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_1058])).
% 51.70/40.00  tff(c_1081, plain, (![B_209]: (r2_hidden(B_209, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_209) | ~m1_subset_1(B_209, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1071])).
% 51.70/40.00  tff(c_1083, plain, (![B_212]: (r2_hidden(B_212, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_212) | ~m1_subset_1(B_212, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1081])).
% 51.70/40.00  tff(c_75655, plain, (![A_1625]: (r1_tarski(A_1625, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', '#skF_1'(A_1625, k1_tops_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_1'(A_1625, k1_tops_1('#skF_2', '#skF_3')), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1083, c_4])).
% 51.70/40.00  tff(c_75699, plain, (![A_1625]: (r1_tarski(A_1625, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', '#skF_1'(A_1625, k1_tops_1('#skF_2', '#skF_3'))) | ~r2_hidden('#skF_1'(A_1625, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_115, c_75655])).
% 51.70/40.00  tff(c_176279, plain, (![A_2900]: (r1_tarski(A_2900, k1_tops_1('#skF_2', '#skF_3')) | ~r2_hidden('#skF_1'(A_2900, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_175964, c_75699])).
% 51.70/40.00  tff(c_176375, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_176279])).
% 51.70/40.00  tff(c_176418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_158, c_176375])).
% 51.70/40.00  tff(c_176419, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_157])).
% 51.70/40.00  tff(c_176459, plain, (![A_2905, B_2906]: (v3_pre_topc(k1_tops_1(A_2905, B_2906), A_2905) | ~m1_subset_1(B_2906, k1_zfmisc_1(u1_struct_0(A_2905))) | ~l1_pre_topc(A_2905) | ~v2_pre_topc(A_2905))), inference(cnfTransformation, [status(thm)], [f_56])).
% 51.70/40.00  tff(c_176464, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_176459])).
% 51.70/40.00  tff(c_176468, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_176419, c_176464])).
% 51.70/40.00  tff(c_176470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_176468])).
% 51.70/40.00  tff(c_176472, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 51.70/40.00  tff(c_42, plain, (![D_63]: (~r1_tarski(D_63, '#skF_3') | ~m1_connsp_2(D_63, '#skF_2', '#skF_4') | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_176687, plain, (![D_2958]: (~r1_tarski(D_2958, '#skF_3') | ~m1_connsp_2(D_2958, '#skF_2', '#skF_4') | ~m1_subset_1(D_2958, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_176472, c_42])).
% 51.70/40.00  tff(c_176698, plain, (~r1_tarski('#skF_3', '#skF_3') | ~m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_176687])).
% 51.70/40.00  tff(c_176703, plain, (~m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_176698])).
% 51.70/40.00  tff(c_176471, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 51.70/40.00  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 51.70/40.00  tff(c_176475, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_176472, c_46])).
% 51.70/40.00  tff(c_177845, plain, (![B_3078, A_3079, C_3080]: (m1_connsp_2(B_3078, A_3079, C_3080) | ~r2_hidden(C_3080, B_3078) | ~v3_pre_topc(B_3078, A_3079) | ~m1_subset_1(C_3080, u1_struct_0(A_3079)) | ~m1_subset_1(B_3078, k1_zfmisc_1(u1_struct_0(A_3079))) | ~l1_pre_topc(A_3079) | ~v2_pre_topc(A_3079) | v2_struct_0(A_3079))), inference(cnfTransformation, [status(thm)], [f_125])).
% 51.70/40.00  tff(c_177864, plain, (![B_3078]: (m1_connsp_2(B_3078, '#skF_2', '#skF_4') | ~r2_hidden('#skF_4', B_3078) | ~v3_pre_topc(B_3078, '#skF_2') | ~m1_subset_1(B_3078, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_176475, c_177845])).
% 51.70/40.00  tff(c_177886, plain, (![B_3078]: (m1_connsp_2(B_3078, '#skF_2', '#skF_4') | ~r2_hidden('#skF_4', B_3078) | ~v3_pre_topc(B_3078, '#skF_2') | ~m1_subset_1(B_3078, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_177864])).
% 51.70/40.00  tff(c_177888, plain, (![B_3081]: (m1_connsp_2(B_3081, '#skF_2', '#skF_4') | ~r2_hidden('#skF_4', B_3081) | ~v3_pre_topc(B_3081, '#skF_2') | ~m1_subset_1(B_3081, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_177886])).
% 51.70/40.00  tff(c_177907, plain, (m1_connsp_2('#skF_3', '#skF_2', '#skF_4') | ~r2_hidden('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_177888])).
% 51.70/40.00  tff(c_177914, plain, (m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176472, c_176471, c_177907])).
% 51.70/40.00  tff(c_177916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176703, c_177914])).
% 51.70/40.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.70/40.00  
% 51.70/40.00  Inference rules
% 51.70/40.00  ----------------------
% 51.70/40.00  #Ref     : 0
% 51.70/40.00  #Sup     : 37294
% 51.70/40.00  #Fact    : 0
% 51.70/40.00  #Define  : 0
% 51.70/40.00  #Split   : 61
% 51.70/40.00  #Chain   : 0
% 51.70/40.00  #Close   : 0
% 51.70/40.00  
% 51.70/40.00  Ordering : KBO
% 51.70/40.00  
% 51.70/40.00  Simplification rules
% 51.70/40.00  ----------------------
% 51.70/40.00  #Subsume      : 18916
% 51.70/40.00  #Demod        : 31046
% 51.70/40.00  #Tautology    : 3581
% 51.70/40.00  #SimpNegUnit  : 1715
% 51.70/40.00  #BackRed      : 50
% 51.70/40.00  
% 51.70/40.00  #Partial instantiations: 0
% 51.70/40.00  #Strategies tried      : 1
% 51.70/40.00  
% 51.70/40.00  Timing (in seconds)
% 51.70/40.00  ----------------------
% 51.70/40.01  Preprocessing        : 0.32
% 51.70/40.01  Parsing              : 0.17
% 51.70/40.01  CNF conversion       : 0.03
% 51.70/40.01  Main loop            : 38.85
% 51.70/40.01  Inferencing          : 4.52
% 51.70/40.01  Reduction            : 9.93
% 51.70/40.01  Demodulation         : 7.20
% 51.70/40.01  BG Simplification    : 0.35
% 51.70/40.01  Subsumption          : 22.25
% 51.70/40.01  Abstraction          : 0.80
% 51.70/40.01  MUC search           : 0.00
% 51.70/40.01  Cooper               : 0.00
% 51.70/40.01  Total                : 39.21
% 51.70/40.01  Index Insertion      : 0.00
% 51.70/40.01  Index Deletion       : 0.00
% 51.70/40.01  Index Matching       : 0.00
% 51.70/40.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
