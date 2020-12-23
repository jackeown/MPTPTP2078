%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:13 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 441 expanded)
%              Number of leaves         :   28 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          :  468 (1778 expanded)
%              Number of equality atoms :   31 (  57 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_87,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_104,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_65,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_59,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_2054,plain,(
    ! [A_240,C_241,B_242] :
      ( r1_tarski(A_240,C_241)
      | ~ r1_tarski(B_242,C_241)
      | ~ r1_tarski(A_240,B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2073,plain,(
    ! [A_244] :
      ( r1_tarski(A_244,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_244,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_63,c_2054])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_57,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_56,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_38,plain,(
    ! [D_64] :
      ( ~ r2_hidden('#skF_2',D_64)
      | ~ r1_tarski(D_64,'#skF_3')
      | ~ v3_pre_topc(D_64,'#skF_1')
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_734,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_20,plain,(
    ! [B_28,D_34,C_32,A_20] :
      ( k1_tops_1(B_28,D_34) = D_34
      | ~ v3_pre_topc(D_34,B_28)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0(B_28)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1123,plain,(
    ! [C_180,A_181] :
      ( ~ m1_subset_1(C_180,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181) ) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_1126,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_1123])).

tff(c_1137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1126])).

tff(c_1269,plain,(
    ! [B_193,D_194] :
      ( k1_tops_1(B_193,D_194) = D_194
      | ~ v3_pre_topc(D_194,B_193)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(u1_struct_0(B_193)))
      | ~ l1_pre_topc(B_193) ) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1272,plain,
    ( k1_tops_1('#skF_1','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_1269])).

tff(c_1282,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_57,c_1272])).

tff(c_16,plain,(
    ! [A_13,B_17,C_19] :
      ( r1_tarski(k1_tops_1(A_13,B_17),k1_tops_1(A_13,C_19))
      | ~ r1_tarski(B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1308,plain,(
    ! [C_19] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_19))
      | ~ r1_tarski('#skF_4',C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_16])).

tff(c_1623,plain,(
    ! [C_216] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_216))
      | ~ r1_tarski('#skF_4',C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_76,c_1308])).

tff(c_1633,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1623])).

tff(c_1640,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1633])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1666,plain,(
    ! [A_217] :
      ( r1_tarski(A_217,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_217,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1640,c_2])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ r1_tarski(k1_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1692,plain,(
    ! [A_4] :
      ( r2_hidden(A_4,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k1_tarski(A_4),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1666,c_4])).

tff(c_1943,plain,(
    ! [C_229,A_230,B_231] :
      ( m1_connsp_2(C_229,A_230,B_231)
      | ~ r2_hidden(B_231,k1_tops_1(A_230,C_229))
      | ~ m1_subset_1(C_229,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ m1_subset_1(B_231,u1_struct_0(A_230))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1947,plain,(
    ! [A_4] :
      ( m1_connsp_2('#skF_3','#skF_1',A_4)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(A_4,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(k1_tarski(A_4),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1692,c_1943])).

tff(c_1958,plain,(
    ! [A_4] :
      ( m1_connsp_2('#skF_3','#skF_1',A_4)
      | ~ m1_subset_1(A_4,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(k1_tarski(A_4),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_1947])).

tff(c_2002,plain,(
    ! [A_234] :
      ( m1_connsp_2('#skF_3','#skF_1',A_234)
      | ~ m1_subset_1(A_234,u1_struct_0('#skF_1'))
      | ~ r1_tarski(k1_tarski(A_234),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1958])).

tff(c_2014,plain,(
    ! [A_236] :
      ( m1_connsp_2('#skF_3','#skF_1',A_236)
      | ~ m1_subset_1(A_236,u1_struct_0('#skF_1'))
      | ~ r2_hidden(A_236,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_2002])).

tff(c_2017,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_2014])).

tff(c_2020,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2017])).

tff(c_2022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_734,c_2020])).

tff(c_2032,plain,(
    ! [D_239] :
      ( ~ r2_hidden('#skF_2',D_239)
      | ~ r1_tarski(D_239,'#skF_3')
      | ~ v3_pre_topc(D_239,'#skF_1')
      | ~ m1_subset_1(D_239,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2035,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_2032])).

tff(c_2046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_65,c_64,c_2035])).

tff(c_2048,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2052,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_2048])).

tff(c_2078,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2073,c_2052])).

tff(c_2087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2078])).

tff(c_2088,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2142,plain,(
    ! [A_262,B_263] :
      ( r1_tarski(k1_tops_1(A_262,B_263),B_263)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2147,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2142])).

tff(c_2151,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2147])).

tff(c_2191,plain,(
    ! [A_271,B_272] :
      ( v3_pre_topc(k1_tops_1(A_271,B_272),A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2196,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2191])).

tff(c_2200,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2196])).

tff(c_2101,plain,(
    ! [A_249,C_250,B_251] :
      ( r1_tarski(A_249,C_250)
      | ~ r1_tarski(B_251,C_250)
      | ~ r1_tarski(A_249,B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2106,plain,(
    ! [A_249] :
      ( r1_tarski(A_249,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_249,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_63,c_2101])).

tff(c_2529,plain,(
    ! [C_346,A_347] :
      ( ~ m1_subset_1(C_346,k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347) ) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_2536,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2529])).

tff(c_2541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2536])).

tff(c_2543,plain,(
    ! [B_348,D_349] :
      ( k1_tops_1(B_348,D_349) = D_349
      | ~ v3_pre_topc(D_349,B_348)
      | ~ m1_subset_1(D_349,k1_zfmisc_1(u1_struct_0(B_348)))
      | ~ l1_pre_topc(B_348) ) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_2556,plain,(
    ! [B_350,A_351] :
      ( k1_tops_1(B_350,A_351) = A_351
      | ~ v3_pre_topc(A_351,B_350)
      | ~ l1_pre_topc(B_350)
      | ~ r1_tarski(A_351,u1_struct_0(B_350)) ) ),
    inference(resolution,[status(thm)],[c_10,c_2543])).

tff(c_2574,plain,(
    ! [A_249] :
      ( k1_tops_1('#skF_1',A_249) = A_249
      | ~ v3_pre_topc(A_249,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_249,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2106,c_2556])).

tff(c_2595,plain,(
    ! [A_352] :
      ( k1_tops_1('#skF_1',A_352) = A_352
      | ~ v3_pre_topc(A_352,'#skF_1')
      | ~ r1_tarski(A_352,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2574])).

tff(c_2602,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2200,c_2595])).

tff(c_2611,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2151,c_2602])).

tff(c_3057,plain,(
    ! [B_375,A_376,C_377] :
      ( r2_hidden(B_375,k1_tops_1(A_376,C_377))
      | ~ m1_connsp_2(C_377,A_376,B_375)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ m1_subset_1(B_375,u1_struct_0(A_376))
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3062,plain,(
    ! [B_375] :
      ( r2_hidden(B_375,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_375)
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_3057])).

tff(c_3066,plain,(
    ! [B_375] :
      ( r2_hidden(B_375,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_375)
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3062])).

tff(c_3068,plain,(
    ! [B_378] :
      ( r2_hidden(B_378,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_378)
      | ~ m1_subset_1(B_378,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3066])).

tff(c_18,plain,(
    ! [C_32,A_20,D_34,B_28] :
      ( v3_pre_topc(C_32,A_20)
      | k1_tops_1(A_20,C_32) != C_32
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0(B_28)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2732,plain,(
    ! [D_353,B_354] :
      ( ~ m1_subset_1(D_353,k1_zfmisc_1(u1_struct_0(B_354)))
      | ~ l1_pre_topc(B_354) ) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_2739,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2732])).

tff(c_2744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2739])).

tff(c_2878,plain,(
    ! [C_363,A_364] :
      ( v3_pre_topc(C_363,A_364)
      | k1_tops_1(A_364,C_363) != C_363
      | ~ m1_subset_1(C_363,k1_zfmisc_1(u1_struct_0(A_364)))
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364) ) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_2965,plain,(
    ! [A_371,A_372] :
      ( v3_pre_topc(A_371,A_372)
      | k1_tops_1(A_372,A_371) != A_371
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | ~ r1_tarski(A_371,u1_struct_0(A_372)) ) ),
    inference(resolution,[status(thm)],[c_10,c_2878])).

tff(c_2995,plain,(
    ! [A_249] :
      ( v3_pre_topc(A_249,'#skF_1')
      | k1_tops_1('#skF_1',A_249) != A_249
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_249,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2106,c_2965])).

tff(c_3029,plain,(
    ! [A_373] :
      ( v3_pre_topc(A_373,'#skF_1')
      | k1_tops_1('#skF_1',A_373) != A_373
      | ~ r1_tarski(A_373,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2995])).

tff(c_2089,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_64] :
      ( ~ r2_hidden('#skF_2',D_64)
      | ~ r1_tarski(D_64,'#skF_3')
      | ~ v3_pre_topc(D_64,'#skF_1')
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2203,plain,(
    ! [D_275] :
      ( ~ r2_hidden('#skF_2',D_275)
      | ~ r1_tarski(D_275,'#skF_3')
      | ~ v3_pre_topc(D_275,'#skF_1')
      | ~ m1_subset_1(D_275,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2089,c_46])).

tff(c_2213,plain,(
    ! [A_276] :
      ( ~ r2_hidden('#skF_2',A_276)
      | ~ r1_tarski(A_276,'#skF_3')
      | ~ v3_pre_topc(A_276,'#skF_1')
      | ~ r1_tarski(A_276,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_2203])).

tff(c_2229,plain,(
    ! [A_249] :
      ( ~ r2_hidden('#skF_2',A_249)
      | ~ v3_pre_topc(A_249,'#skF_1')
      | ~ r1_tarski(A_249,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2106,c_2213])).

tff(c_3041,plain,(
    ! [A_373] :
      ( ~ r2_hidden('#skF_2',A_373)
      | k1_tops_1('#skF_1',A_373) != A_373
      | ~ r1_tarski(A_373,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3029,c_2229])).

tff(c_3072,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) != k1_tops_1('#skF_1','#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3068,c_3041])).

tff(c_3109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2088,c_2151,c_2611,c_3072])).

tff(c_3110,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_3172,plain,(
    ! [A_392,B_393] :
      ( r1_tarski(k1_tops_1(A_392,B_393),B_393)
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0(A_392)))
      | ~ l1_pre_topc(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3177,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_3172])).

tff(c_3181,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3177])).

tff(c_4238,plain,(
    ! [B_494,A_495,C_496] :
      ( r2_hidden(B_494,k1_tops_1(A_495,C_496))
      | ~ m1_connsp_2(C_496,A_495,B_494)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(u1_struct_0(A_495)))
      | ~ m1_subset_1(B_494,u1_struct_0(A_495))
      | ~ l1_pre_topc(A_495)
      | ~ v2_pre_topc(A_495)
      | v2_struct_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4245,plain,(
    ! [B_494] :
      ( r2_hidden(B_494,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_494)
      | ~ m1_subset_1(B_494,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_4238])).

tff(c_4253,plain,(
    ! [B_494] :
      ( r2_hidden(B_494,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_494)
      | ~ m1_subset_1(B_494,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4245])).

tff(c_4262,plain,(
    ! [B_498] :
      ( r2_hidden(B_498,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_498)
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_4253])).

tff(c_3240,plain,(
    ! [A_403,B_404] :
      ( v3_pre_topc(k1_tops_1(A_403,B_404),A_403)
      | ~ m1_subset_1(B_404,k1_zfmisc_1(u1_struct_0(A_403)))
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3246,plain,(
    ! [A_403,A_6] :
      ( v3_pre_topc(k1_tops_1(A_403,A_6),A_403)
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | ~ r1_tarski(A_6,u1_struct_0(A_403)) ) ),
    inference(resolution,[status(thm)],[c_10,c_3240])).

tff(c_3124,plain,(
    ! [A_383,C_384,B_385] :
      ( r1_tarski(A_383,C_384)
      | ~ r1_tarski(B_385,C_384)
      | ~ r1_tarski(A_383,B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3131,plain,(
    ! [A_383] :
      ( r1_tarski(A_383,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_383,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_63,c_3124])).

tff(c_3111,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_64] :
      ( ~ r2_hidden('#skF_2',D_64)
      | ~ r1_tarski(D_64,'#skF_3')
      | ~ v3_pre_topc(D_64,'#skF_1')
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3153,plain,(
    ! [D_388] :
      ( ~ r2_hidden('#skF_2',D_388)
      | ~ r1_tarski(D_388,'#skF_3')
      | ~ v3_pre_topc(D_388,'#skF_1')
      | ~ m1_subset_1(D_388,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3111,c_42])).

tff(c_3300,plain,(
    ! [A_418] :
      ( ~ r2_hidden('#skF_2',A_418)
      | ~ r1_tarski(A_418,'#skF_3')
      | ~ v3_pre_topc(A_418,'#skF_1')
      | ~ r1_tarski(A_418,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_3153])).

tff(c_3319,plain,(
    ! [A_419] :
      ( ~ r2_hidden('#skF_2',A_419)
      | ~ v3_pre_topc(A_419,'#skF_1')
      | ~ r1_tarski(A_419,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3131,c_3300])).

tff(c_3323,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_6))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_6),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_3246,c_3319])).

tff(c_3332,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_6))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_6),'#skF_3')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3323])).

tff(c_4284,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4262,c_3332])).

tff(c_4316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3110,c_63,c_3181,c_4284])).

tff(c_4317,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4373,plain,(
    ! [A_514,B_515] :
      ( r1_tarski(k1_tops_1(A_514,B_515),B_515)
      | ~ m1_subset_1(B_515,k1_zfmisc_1(u1_struct_0(A_514)))
      | ~ l1_pre_topc(A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4378,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_4373])).

tff(c_4382,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4378])).

tff(c_4427,plain,(
    ! [A_521,B_522] :
      ( v3_pre_topc(k1_tops_1(A_521,B_522),A_521)
      | ~ m1_subset_1(B_522,k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4432,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_4427])).

tff(c_4436,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4432])).

tff(c_4326,plain,(
    ! [A_503,B_504] :
      ( r1_tarski(A_503,B_504)
      | ~ m1_subset_1(A_503,k1_zfmisc_1(B_504)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4330,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_4326])).

tff(c_4338,plain,(
    ! [A_507,C_508,B_509] :
      ( r1_tarski(A_507,C_508)
      | ~ r1_tarski(B_509,C_508)
      | ~ r1_tarski(A_507,B_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4345,plain,(
    ! [A_507] :
      ( r1_tarski(A_507,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_507,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4330,c_4338])).

tff(c_4811,plain,(
    ! [C_584,A_585] :
      ( ~ m1_subset_1(C_584,k1_zfmisc_1(u1_struct_0(A_585)))
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585) ) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_4818,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_4811])).

tff(c_4823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4818])).

tff(c_4841,plain,(
    ! [B_586,D_587] :
      ( k1_tops_1(B_586,D_587) = D_587
      | ~ v3_pre_topc(D_587,B_586)
      | ~ m1_subset_1(D_587,k1_zfmisc_1(u1_struct_0(B_586)))
      | ~ l1_pre_topc(B_586) ) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_4854,plain,(
    ! [B_588,A_589] :
      ( k1_tops_1(B_588,A_589) = A_589
      | ~ v3_pre_topc(A_589,B_588)
      | ~ l1_pre_topc(B_588)
      | ~ r1_tarski(A_589,u1_struct_0(B_588)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4841])).

tff(c_4868,plain,(
    ! [A_507] :
      ( k1_tops_1('#skF_1',A_507) = A_507
      | ~ v3_pre_topc(A_507,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_507,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4345,c_4854])).

tff(c_4889,plain,(
    ! [A_590] :
      ( k1_tops_1('#skF_1',A_590) = A_590
      | ~ v3_pre_topc(A_590,'#skF_1')
      | ~ r1_tarski(A_590,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4868])).

tff(c_4899,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4436,c_4889])).

tff(c_4906,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4382,c_4899])).

tff(c_5084,plain,(
    ! [B_595,A_596,C_597] :
      ( r2_hidden(B_595,k1_tops_1(A_596,C_597))
      | ~ m1_connsp_2(C_597,A_596,B_595)
      | ~ m1_subset_1(C_597,k1_zfmisc_1(u1_struct_0(A_596)))
      | ~ m1_subset_1(B_595,u1_struct_0(A_596))
      | ~ l1_pre_topc(A_596)
      | ~ v2_pre_topc(A_596)
      | v2_struct_0(A_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5089,plain,(
    ! [B_595] :
      ( r2_hidden(B_595,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_595)
      | ~ m1_subset_1(B_595,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_5084])).

tff(c_5093,plain,(
    ! [B_595] :
      ( r2_hidden(B_595,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_595)
      | ~ m1_subset_1(B_595,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_5089])).

tff(c_5122,plain,(
    ! [B_600] :
      ( r2_hidden(B_600,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_600)
      | ~ m1_subset_1(B_600,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_5093])).

tff(c_4705,plain,(
    ! [D_576,B_577] :
      ( ~ m1_subset_1(D_576,k1_zfmisc_1(u1_struct_0(B_577)))
      | ~ l1_pre_topc(B_577) ) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_4712,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_4705])).

tff(c_4717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4712])).

tff(c_4719,plain,(
    ! [C_578,A_579] :
      ( v3_pre_topc(C_578,A_579)
      | k1_tops_1(A_579,C_578) != C_578
      | ~ m1_subset_1(C_578,k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ l1_pre_topc(A_579)
      | ~ v2_pre_topc(A_579) ) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_4732,plain,(
    ! [A_580,A_581] :
      ( v3_pre_topc(A_580,A_581)
      | k1_tops_1(A_581,A_580) != A_580
      | ~ l1_pre_topc(A_581)
      | ~ v2_pre_topc(A_581)
      | ~ r1_tarski(A_580,u1_struct_0(A_581)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4719])).

tff(c_4746,plain,(
    ! [A_507] :
      ( v3_pre_topc(A_507,'#skF_1')
      | k1_tops_1('#skF_1',A_507) != A_507
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_507,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4345,c_4732])).

tff(c_4767,plain,(
    ! [A_582] :
      ( v3_pre_topc(A_582,'#skF_1')
      | k1_tops_1('#skF_1',A_582) != A_582
      | ~ r1_tarski(A_582,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4746])).

tff(c_4318,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [D_64] :
      ( ~ r2_hidden('#skF_2',D_64)
      | ~ r1_tarski(D_64,'#skF_3')
      | ~ v3_pre_topc(D_64,'#skF_1')
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4394,plain,(
    ! [D_518] :
      ( ~ r2_hidden('#skF_2',D_518)
      | ~ r1_tarski(D_518,'#skF_3')
      | ~ v3_pre_topc(D_518,'#skF_1')
      | ~ m1_subset_1(D_518,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4318,c_50])).

tff(c_4512,plain,(
    ! [A_540] :
      ( ~ r2_hidden('#skF_2',A_540)
      | ~ r1_tarski(A_540,'#skF_3')
      | ~ v3_pre_topc(A_540,'#skF_1')
      | ~ r1_tarski(A_540,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_4394])).

tff(c_4528,plain,(
    ! [A_507] :
      ( ~ r2_hidden('#skF_2',A_507)
      | ~ v3_pre_topc(A_507,'#skF_1')
      | ~ r1_tarski(A_507,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4345,c_4512])).

tff(c_4777,plain,(
    ! [A_582] :
      ( ~ r2_hidden('#skF_2',A_582)
      | k1_tops_1('#skF_1',A_582) != A_582
      | ~ r1_tarski(A_582,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4767,c_4528])).

tff(c_5131,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) != k1_tops_1('#skF_1','#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_5122,c_4777])).

tff(c_5159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4317,c_4382,c_4906,c_5131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:34:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.24  
% 6.04/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.25  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.04/2.25  
% 6.04/2.25  %Foreground sorts:
% 6.04/2.25  
% 6.04/2.25  
% 6.04/2.25  %Background operators:
% 6.04/2.25  
% 6.04/2.25  
% 6.04/2.25  %Foreground operators:
% 6.04/2.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.04/2.25  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.04/2.25  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.04/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.04/2.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.04/2.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.04/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.04/2.25  tff('#skF_2', type, '#skF_2': $i).
% 6.04/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.04/2.25  tff('#skF_1', type, '#skF_1': $i).
% 6.04/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.04/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.25  tff('#skF_4', type, '#skF_4': $i).
% 6.04/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.04/2.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.04/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.04/2.25  
% 6.42/2.28  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 6.42/2.28  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.42/2.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.42/2.28  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.42/2.28  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 6.42/2.28  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 6.42/2.28  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 6.42/2.28  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 6.42/2.28  tff(f_47, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.42/2.28  tff(c_30, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_48, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_65, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 6.42/2.28  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_59, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.42/2.28  tff(c_63, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_59])).
% 6.42/2.28  tff(c_2054, plain, (![A_240, C_241, B_242]: (r1_tarski(A_240, C_241) | ~r1_tarski(B_242, C_241) | ~r1_tarski(A_240, B_242))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.42/2.28  tff(c_2073, plain, (![A_244]: (r1_tarski(A_244, u1_struct_0('#skF_1')) | ~r1_tarski(A_244, '#skF_3'))), inference(resolution, [status(thm)], [c_63, c_2054])).
% 6.42/2.28  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.42/2.28  tff(c_52, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_57, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 6.42/2.28  tff(c_44, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_64, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 6.42/2.28  tff(c_56, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_56])).
% 6.42/2.28  tff(c_38, plain, (![D_64]: (~r2_hidden('#skF_2', D_64) | ~r1_tarski(D_64, '#skF_3') | ~v3_pre_topc(D_64, '#skF_1') | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_734, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 6.42/2.28  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.42/2.28  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_20, plain, (![B_28, D_34, C_32, A_20]: (k1_tops_1(B_28, D_34)=D_34 | ~v3_pre_topc(D_34, B_28) | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0(B_28))) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(B_28) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.42/2.28  tff(c_1123, plain, (![C_180, A_181]: (~m1_subset_1(C_180, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181))), inference(splitLeft, [status(thm)], [c_20])).
% 6.42/2.28  tff(c_1126, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_1123])).
% 6.42/2.28  tff(c_1137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1126])).
% 6.42/2.28  tff(c_1269, plain, (![B_193, D_194]: (k1_tops_1(B_193, D_194)=D_194 | ~v3_pre_topc(D_194, B_193) | ~m1_subset_1(D_194, k1_zfmisc_1(u1_struct_0(B_193))) | ~l1_pre_topc(B_193))), inference(splitRight, [status(thm)], [c_20])).
% 6.42/2.28  tff(c_1272, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_1269])).
% 6.42/2.28  tff(c_1282, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_57, c_1272])).
% 6.42/2.28  tff(c_16, plain, (![A_13, B_17, C_19]: (r1_tarski(k1_tops_1(A_13, B_17), k1_tops_1(A_13, C_19)) | ~r1_tarski(B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.42/2.28  tff(c_1308, plain, (![C_19]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_19)) | ~r1_tarski('#skF_4', C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1282, c_16])).
% 6.42/2.28  tff(c_1623, plain, (![C_216]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_216)) | ~r1_tarski('#skF_4', C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_76, c_1308])).
% 6.42/2.28  tff(c_1633, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_1623])).
% 6.42/2.28  tff(c_1640, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1633])).
% 6.42/2.28  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.42/2.28  tff(c_1666, plain, (![A_217]: (r1_tarski(A_217, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_217, '#skF_4'))), inference(resolution, [status(thm)], [c_1640, c_2])).
% 6.42/2.28  tff(c_4, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~r1_tarski(k1_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.42/2.28  tff(c_1692, plain, (![A_4]: (r2_hidden(A_4, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tarski(A_4), '#skF_4'))), inference(resolution, [status(thm)], [c_1666, c_4])).
% 6.42/2.28  tff(c_1943, plain, (![C_229, A_230, B_231]: (m1_connsp_2(C_229, A_230, B_231) | ~r2_hidden(B_231, k1_tops_1(A_230, C_229)) | ~m1_subset_1(C_229, k1_zfmisc_1(u1_struct_0(A_230))) | ~m1_subset_1(B_231, u1_struct_0(A_230)) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.42/2.28  tff(c_1947, plain, (![A_4]: (m1_connsp_2('#skF_3', '#skF_1', A_4) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(A_4, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski(k1_tarski(A_4), '#skF_4'))), inference(resolution, [status(thm)], [c_1692, c_1943])).
% 6.42/2.28  tff(c_1958, plain, (![A_4]: (m1_connsp_2('#skF_3', '#skF_1', A_4) | ~m1_subset_1(A_4, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1') | ~r1_tarski(k1_tarski(A_4), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_1947])).
% 6.42/2.28  tff(c_2002, plain, (![A_234]: (m1_connsp_2('#skF_3', '#skF_1', A_234) | ~m1_subset_1(A_234, u1_struct_0('#skF_1')) | ~r1_tarski(k1_tarski(A_234), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_1958])).
% 6.42/2.28  tff(c_2014, plain, (![A_236]: (m1_connsp_2('#skF_3', '#skF_1', A_236) | ~m1_subset_1(A_236, u1_struct_0('#skF_1')) | ~r2_hidden(A_236, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_2002])).
% 6.42/2.28  tff(c_2017, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_2014])).
% 6.42/2.28  tff(c_2020, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2017])).
% 6.42/2.28  tff(c_2022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_734, c_2020])).
% 6.42/2.28  tff(c_2032, plain, (![D_239]: (~r2_hidden('#skF_2', D_239) | ~r1_tarski(D_239, '#skF_3') | ~v3_pre_topc(D_239, '#skF_1') | ~m1_subset_1(D_239, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_38])).
% 6.42/2.28  tff(c_2035, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_2032])).
% 6.42/2.28  tff(c_2046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_65, c_64, c_2035])).
% 6.42/2.28  tff(c_2048, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 6.42/2.28  tff(c_2052, plain, (~r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_2048])).
% 6.42/2.28  tff(c_2078, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2073, c_2052])).
% 6.42/2.28  tff(c_2087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_2078])).
% 6.42/2.28  tff(c_2088, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.42/2.28  tff(c_2142, plain, (![A_262, B_263]: (r1_tarski(k1_tops_1(A_262, B_263), B_263) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.42/2.28  tff(c_2147, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2142])).
% 6.42/2.28  tff(c_2151, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2147])).
% 6.42/2.28  tff(c_2191, plain, (![A_271, B_272]: (v3_pre_topc(k1_tops_1(A_271, B_272), A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.42/2.28  tff(c_2196, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2191])).
% 6.42/2.28  tff(c_2200, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2196])).
% 6.42/2.28  tff(c_2101, plain, (![A_249, C_250, B_251]: (r1_tarski(A_249, C_250) | ~r1_tarski(B_251, C_250) | ~r1_tarski(A_249, B_251))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.42/2.28  tff(c_2106, plain, (![A_249]: (r1_tarski(A_249, u1_struct_0('#skF_1')) | ~r1_tarski(A_249, '#skF_3'))), inference(resolution, [status(thm)], [c_63, c_2101])).
% 6.42/2.28  tff(c_2529, plain, (![C_346, A_347]: (~m1_subset_1(C_346, k1_zfmisc_1(u1_struct_0(A_347))) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347))), inference(splitLeft, [status(thm)], [c_20])).
% 6.42/2.28  tff(c_2536, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2529])).
% 6.42/2.28  tff(c_2541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2536])).
% 6.42/2.28  tff(c_2543, plain, (![B_348, D_349]: (k1_tops_1(B_348, D_349)=D_349 | ~v3_pre_topc(D_349, B_348) | ~m1_subset_1(D_349, k1_zfmisc_1(u1_struct_0(B_348))) | ~l1_pre_topc(B_348))), inference(splitRight, [status(thm)], [c_20])).
% 6.42/2.28  tff(c_2556, plain, (![B_350, A_351]: (k1_tops_1(B_350, A_351)=A_351 | ~v3_pre_topc(A_351, B_350) | ~l1_pre_topc(B_350) | ~r1_tarski(A_351, u1_struct_0(B_350)))), inference(resolution, [status(thm)], [c_10, c_2543])).
% 6.42/2.28  tff(c_2574, plain, (![A_249]: (k1_tops_1('#skF_1', A_249)=A_249 | ~v3_pre_topc(A_249, '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_249, '#skF_3'))), inference(resolution, [status(thm)], [c_2106, c_2556])).
% 6.42/2.28  tff(c_2595, plain, (![A_352]: (k1_tops_1('#skF_1', A_352)=A_352 | ~v3_pre_topc(A_352, '#skF_1') | ~r1_tarski(A_352, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2574])).
% 6.42/2.28  tff(c_2602, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_2200, c_2595])).
% 6.42/2.28  tff(c_2611, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2151, c_2602])).
% 6.42/2.28  tff(c_3057, plain, (![B_375, A_376, C_377]: (r2_hidden(B_375, k1_tops_1(A_376, C_377)) | ~m1_connsp_2(C_377, A_376, B_375) | ~m1_subset_1(C_377, k1_zfmisc_1(u1_struct_0(A_376))) | ~m1_subset_1(B_375, u1_struct_0(A_376)) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376) | v2_struct_0(A_376))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.42/2.28  tff(c_3062, plain, (![B_375]: (r2_hidden(B_375, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_375) | ~m1_subset_1(B_375, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_3057])).
% 6.42/2.28  tff(c_3066, plain, (![B_375]: (r2_hidden(B_375, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_375) | ~m1_subset_1(B_375, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3062])).
% 6.42/2.28  tff(c_3068, plain, (![B_378]: (r2_hidden(B_378, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_378) | ~m1_subset_1(B_378, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_3066])).
% 6.42/2.28  tff(c_18, plain, (![C_32, A_20, D_34, B_28]: (v3_pre_topc(C_32, A_20) | k1_tops_1(A_20, C_32)!=C_32 | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0(B_28))) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(B_28) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.42/2.28  tff(c_2732, plain, (![D_353, B_354]: (~m1_subset_1(D_353, k1_zfmisc_1(u1_struct_0(B_354))) | ~l1_pre_topc(B_354))), inference(splitLeft, [status(thm)], [c_18])).
% 6.42/2.28  tff(c_2739, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2732])).
% 6.42/2.28  tff(c_2744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_2739])).
% 6.42/2.28  tff(c_2878, plain, (![C_363, A_364]: (v3_pre_topc(C_363, A_364) | k1_tops_1(A_364, C_363)!=C_363 | ~m1_subset_1(C_363, k1_zfmisc_1(u1_struct_0(A_364))) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364))), inference(splitRight, [status(thm)], [c_18])).
% 6.42/2.28  tff(c_2965, plain, (![A_371, A_372]: (v3_pre_topc(A_371, A_372) | k1_tops_1(A_372, A_371)!=A_371 | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | ~r1_tarski(A_371, u1_struct_0(A_372)))), inference(resolution, [status(thm)], [c_10, c_2878])).
% 6.42/2.28  tff(c_2995, plain, (![A_249]: (v3_pre_topc(A_249, '#skF_1') | k1_tops_1('#skF_1', A_249)!=A_249 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_249, '#skF_3'))), inference(resolution, [status(thm)], [c_2106, c_2965])).
% 6.42/2.28  tff(c_3029, plain, (![A_373]: (v3_pre_topc(A_373, '#skF_1') | k1_tops_1('#skF_1', A_373)!=A_373 | ~r1_tarski(A_373, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2995])).
% 6.42/2.28  tff(c_2089, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 6.42/2.28  tff(c_46, plain, (![D_64]: (~r2_hidden('#skF_2', D_64) | ~r1_tarski(D_64, '#skF_3') | ~v3_pre_topc(D_64, '#skF_1') | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_2203, plain, (![D_275]: (~r2_hidden('#skF_2', D_275) | ~r1_tarski(D_275, '#skF_3') | ~v3_pre_topc(D_275, '#skF_1') | ~m1_subset_1(D_275, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2089, c_46])).
% 6.42/2.28  tff(c_2213, plain, (![A_276]: (~r2_hidden('#skF_2', A_276) | ~r1_tarski(A_276, '#skF_3') | ~v3_pre_topc(A_276, '#skF_1') | ~r1_tarski(A_276, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_2203])).
% 6.42/2.28  tff(c_2229, plain, (![A_249]: (~r2_hidden('#skF_2', A_249) | ~v3_pre_topc(A_249, '#skF_1') | ~r1_tarski(A_249, '#skF_3'))), inference(resolution, [status(thm)], [c_2106, c_2213])).
% 6.42/2.28  tff(c_3041, plain, (![A_373]: (~r2_hidden('#skF_2', A_373) | k1_tops_1('#skF_1', A_373)!=A_373 | ~r1_tarski(A_373, '#skF_3'))), inference(resolution, [status(thm)], [c_3029, c_2229])).
% 6.42/2.28  tff(c_3072, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))!=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3068, c_3041])).
% 6.42/2.28  tff(c_3109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2088, c_2151, c_2611, c_3072])).
% 6.42/2.28  tff(c_3110, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 6.42/2.28  tff(c_3172, plain, (![A_392, B_393]: (r1_tarski(k1_tops_1(A_392, B_393), B_393) | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0(A_392))) | ~l1_pre_topc(A_392))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.42/2.28  tff(c_3177, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_3172])).
% 6.42/2.28  tff(c_3181, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3177])).
% 6.42/2.28  tff(c_4238, plain, (![B_494, A_495, C_496]: (r2_hidden(B_494, k1_tops_1(A_495, C_496)) | ~m1_connsp_2(C_496, A_495, B_494) | ~m1_subset_1(C_496, k1_zfmisc_1(u1_struct_0(A_495))) | ~m1_subset_1(B_494, u1_struct_0(A_495)) | ~l1_pre_topc(A_495) | ~v2_pre_topc(A_495) | v2_struct_0(A_495))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.42/2.28  tff(c_4245, plain, (![B_494]: (r2_hidden(B_494, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_494) | ~m1_subset_1(B_494, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_4238])).
% 6.42/2.28  tff(c_4253, plain, (![B_494]: (r2_hidden(B_494, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_494) | ~m1_subset_1(B_494, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4245])).
% 6.42/2.28  tff(c_4262, plain, (![B_498]: (r2_hidden(B_498, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_498) | ~m1_subset_1(B_498, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_4253])).
% 6.42/2.28  tff(c_3240, plain, (![A_403, B_404]: (v3_pre_topc(k1_tops_1(A_403, B_404), A_403) | ~m1_subset_1(B_404, k1_zfmisc_1(u1_struct_0(A_403))) | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.42/2.28  tff(c_3246, plain, (![A_403, A_6]: (v3_pre_topc(k1_tops_1(A_403, A_6), A_403) | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403) | ~r1_tarski(A_6, u1_struct_0(A_403)))), inference(resolution, [status(thm)], [c_10, c_3240])).
% 6.42/2.28  tff(c_3124, plain, (![A_383, C_384, B_385]: (r1_tarski(A_383, C_384) | ~r1_tarski(B_385, C_384) | ~r1_tarski(A_383, B_385))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.42/2.28  tff(c_3131, plain, (![A_383]: (r1_tarski(A_383, u1_struct_0('#skF_1')) | ~r1_tarski(A_383, '#skF_3'))), inference(resolution, [status(thm)], [c_63, c_3124])).
% 6.42/2.28  tff(c_3111, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 6.42/2.28  tff(c_42, plain, (![D_64]: (~r2_hidden('#skF_2', D_64) | ~r1_tarski(D_64, '#skF_3') | ~v3_pre_topc(D_64, '#skF_1') | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_3153, plain, (![D_388]: (~r2_hidden('#skF_2', D_388) | ~r1_tarski(D_388, '#skF_3') | ~v3_pre_topc(D_388, '#skF_1') | ~m1_subset_1(D_388, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_3111, c_42])).
% 6.42/2.28  tff(c_3300, plain, (![A_418]: (~r2_hidden('#skF_2', A_418) | ~r1_tarski(A_418, '#skF_3') | ~v3_pre_topc(A_418, '#skF_1') | ~r1_tarski(A_418, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_3153])).
% 6.42/2.28  tff(c_3319, plain, (![A_419]: (~r2_hidden('#skF_2', A_419) | ~v3_pre_topc(A_419, '#skF_1') | ~r1_tarski(A_419, '#skF_3'))), inference(resolution, [status(thm)], [c_3131, c_3300])).
% 6.42/2.28  tff(c_3323, plain, (![A_6]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_6)) | ~r1_tarski(k1_tops_1('#skF_1', A_6), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_6, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_3246, c_3319])).
% 6.42/2.28  tff(c_3332, plain, (![A_6]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_6)) | ~r1_tarski(k1_tops_1('#skF_1', A_6), '#skF_3') | ~r1_tarski(A_6, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3323])).
% 6.42/2.28  tff(c_4284, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4262, c_3332])).
% 6.42/2.28  tff(c_4316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_3110, c_63, c_3181, c_4284])).
% 6.42/2.28  tff(c_4317, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 6.42/2.28  tff(c_4373, plain, (![A_514, B_515]: (r1_tarski(k1_tops_1(A_514, B_515), B_515) | ~m1_subset_1(B_515, k1_zfmisc_1(u1_struct_0(A_514))) | ~l1_pre_topc(A_514))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.42/2.28  tff(c_4378, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_4373])).
% 6.42/2.28  tff(c_4382, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4378])).
% 6.42/2.28  tff(c_4427, plain, (![A_521, B_522]: (v3_pre_topc(k1_tops_1(A_521, B_522), A_521) | ~m1_subset_1(B_522, k1_zfmisc_1(u1_struct_0(A_521))) | ~l1_pre_topc(A_521) | ~v2_pre_topc(A_521))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.42/2.28  tff(c_4432, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_4427])).
% 6.42/2.28  tff(c_4436, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4432])).
% 6.42/2.28  tff(c_4326, plain, (![A_503, B_504]: (r1_tarski(A_503, B_504) | ~m1_subset_1(A_503, k1_zfmisc_1(B_504)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.42/2.28  tff(c_4330, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_4326])).
% 6.42/2.28  tff(c_4338, plain, (![A_507, C_508, B_509]: (r1_tarski(A_507, C_508) | ~r1_tarski(B_509, C_508) | ~r1_tarski(A_507, B_509))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.42/2.28  tff(c_4345, plain, (![A_507]: (r1_tarski(A_507, u1_struct_0('#skF_1')) | ~r1_tarski(A_507, '#skF_3'))), inference(resolution, [status(thm)], [c_4330, c_4338])).
% 6.42/2.28  tff(c_4811, plain, (![C_584, A_585]: (~m1_subset_1(C_584, k1_zfmisc_1(u1_struct_0(A_585))) | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585))), inference(splitLeft, [status(thm)], [c_20])).
% 6.42/2.28  tff(c_4818, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_4811])).
% 6.42/2.28  tff(c_4823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4818])).
% 6.42/2.28  tff(c_4841, plain, (![B_586, D_587]: (k1_tops_1(B_586, D_587)=D_587 | ~v3_pre_topc(D_587, B_586) | ~m1_subset_1(D_587, k1_zfmisc_1(u1_struct_0(B_586))) | ~l1_pre_topc(B_586))), inference(splitRight, [status(thm)], [c_20])).
% 6.42/2.28  tff(c_4854, plain, (![B_588, A_589]: (k1_tops_1(B_588, A_589)=A_589 | ~v3_pre_topc(A_589, B_588) | ~l1_pre_topc(B_588) | ~r1_tarski(A_589, u1_struct_0(B_588)))), inference(resolution, [status(thm)], [c_10, c_4841])).
% 6.42/2.28  tff(c_4868, plain, (![A_507]: (k1_tops_1('#skF_1', A_507)=A_507 | ~v3_pre_topc(A_507, '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_507, '#skF_3'))), inference(resolution, [status(thm)], [c_4345, c_4854])).
% 6.42/2.28  tff(c_4889, plain, (![A_590]: (k1_tops_1('#skF_1', A_590)=A_590 | ~v3_pre_topc(A_590, '#skF_1') | ~r1_tarski(A_590, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4868])).
% 6.42/2.28  tff(c_4899, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_4436, c_4889])).
% 6.42/2.28  tff(c_4906, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4382, c_4899])).
% 6.42/2.28  tff(c_5084, plain, (![B_595, A_596, C_597]: (r2_hidden(B_595, k1_tops_1(A_596, C_597)) | ~m1_connsp_2(C_597, A_596, B_595) | ~m1_subset_1(C_597, k1_zfmisc_1(u1_struct_0(A_596))) | ~m1_subset_1(B_595, u1_struct_0(A_596)) | ~l1_pre_topc(A_596) | ~v2_pre_topc(A_596) | v2_struct_0(A_596))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.42/2.28  tff(c_5089, plain, (![B_595]: (r2_hidden(B_595, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_595) | ~m1_subset_1(B_595, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_5084])).
% 6.42/2.28  tff(c_5093, plain, (![B_595]: (r2_hidden(B_595, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_595) | ~m1_subset_1(B_595, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_5089])).
% 6.42/2.28  tff(c_5122, plain, (![B_600]: (r2_hidden(B_600, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_600) | ~m1_subset_1(B_600, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_5093])).
% 6.42/2.28  tff(c_4705, plain, (![D_576, B_577]: (~m1_subset_1(D_576, k1_zfmisc_1(u1_struct_0(B_577))) | ~l1_pre_topc(B_577))), inference(splitLeft, [status(thm)], [c_18])).
% 6.42/2.28  tff(c_4712, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_4705])).
% 6.42/2.28  tff(c_4717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_4712])).
% 6.42/2.28  tff(c_4719, plain, (![C_578, A_579]: (v3_pre_topc(C_578, A_579) | k1_tops_1(A_579, C_578)!=C_578 | ~m1_subset_1(C_578, k1_zfmisc_1(u1_struct_0(A_579))) | ~l1_pre_topc(A_579) | ~v2_pre_topc(A_579))), inference(splitRight, [status(thm)], [c_18])).
% 6.42/2.28  tff(c_4732, plain, (![A_580, A_581]: (v3_pre_topc(A_580, A_581) | k1_tops_1(A_581, A_580)!=A_580 | ~l1_pre_topc(A_581) | ~v2_pre_topc(A_581) | ~r1_tarski(A_580, u1_struct_0(A_581)))), inference(resolution, [status(thm)], [c_10, c_4719])).
% 6.42/2.28  tff(c_4746, plain, (![A_507]: (v3_pre_topc(A_507, '#skF_1') | k1_tops_1('#skF_1', A_507)!=A_507 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_507, '#skF_3'))), inference(resolution, [status(thm)], [c_4345, c_4732])).
% 6.42/2.28  tff(c_4767, plain, (![A_582]: (v3_pre_topc(A_582, '#skF_1') | k1_tops_1('#skF_1', A_582)!=A_582 | ~r1_tarski(A_582, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4746])).
% 6.42/2.28  tff(c_4318, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 6.42/2.28  tff(c_50, plain, (![D_64]: (~r2_hidden('#skF_2', D_64) | ~r1_tarski(D_64, '#skF_3') | ~v3_pre_topc(D_64, '#skF_1') | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.42/2.28  tff(c_4394, plain, (![D_518]: (~r2_hidden('#skF_2', D_518) | ~r1_tarski(D_518, '#skF_3') | ~v3_pre_topc(D_518, '#skF_1') | ~m1_subset_1(D_518, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_4318, c_50])).
% 6.42/2.28  tff(c_4512, plain, (![A_540]: (~r2_hidden('#skF_2', A_540) | ~r1_tarski(A_540, '#skF_3') | ~v3_pre_topc(A_540, '#skF_1') | ~r1_tarski(A_540, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_4394])).
% 6.42/2.28  tff(c_4528, plain, (![A_507]: (~r2_hidden('#skF_2', A_507) | ~v3_pre_topc(A_507, '#skF_1') | ~r1_tarski(A_507, '#skF_3'))), inference(resolution, [status(thm)], [c_4345, c_4512])).
% 6.42/2.28  tff(c_4777, plain, (![A_582]: (~r2_hidden('#skF_2', A_582) | k1_tops_1('#skF_1', A_582)!=A_582 | ~r1_tarski(A_582, '#skF_3'))), inference(resolution, [status(thm)], [c_4767, c_4528])).
% 6.42/2.28  tff(c_5131, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))!=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_5122, c_4777])).
% 6.42/2.28  tff(c_5159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4317, c_4382, c_4906, c_5131])).
% 6.42/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.28  
% 6.42/2.28  Inference rules
% 6.42/2.28  ----------------------
% 6.42/2.28  #Ref     : 0
% 6.42/2.28  #Sup     : 1146
% 6.42/2.28  #Fact    : 0
% 6.42/2.28  #Define  : 0
% 6.42/2.28  #Split   : 41
% 6.42/2.28  #Chain   : 0
% 6.42/2.28  #Close   : 0
% 6.42/2.28  
% 6.42/2.28  Ordering : KBO
% 6.42/2.28  
% 6.42/2.28  Simplification rules
% 6.42/2.28  ----------------------
% 6.42/2.28  #Subsume      : 379
% 6.42/2.28  #Demod        : 671
% 6.42/2.28  #Tautology    : 204
% 6.42/2.28  #SimpNegUnit  : 31
% 6.42/2.28  #BackRed      : 18
% 6.42/2.28  
% 6.42/2.28  #Partial instantiations: 0
% 6.42/2.28  #Strategies tried      : 1
% 6.42/2.28  
% 6.42/2.28  Timing (in seconds)
% 6.42/2.28  ----------------------
% 6.42/2.28  Preprocessing        : 0.32
% 6.42/2.28  Parsing              : 0.18
% 6.42/2.28  CNF conversion       : 0.03
% 6.42/2.28  Main loop            : 1.12
% 6.42/2.28  Inferencing          : 0.39
% 6.42/2.28  Reduction            : 0.34
% 6.42/2.28  Demodulation         : 0.21
% 6.42/2.28  BG Simplification    : 0.04
% 6.42/2.28  Subsumption          : 0.27
% 6.42/2.28  Abstraction          : 0.04
% 6.42/2.28  MUC search           : 0.00
% 6.42/2.28  Cooper               : 0.00
% 6.42/2.28  Total                : 1.50
% 6.42/2.28  Index Insertion      : 0.00
% 6.42/2.28  Index Deletion       : 0.00
% 6.42/2.28  Index Matching       : 0.00
% 6.42/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
