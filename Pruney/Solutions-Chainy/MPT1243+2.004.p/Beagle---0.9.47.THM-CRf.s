%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:50 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 257 expanded)
%              Number of leaves         :   25 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  228 ( 947 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> ! [C] :
                  ( r2_hidden(C,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,B)
                      & r2_hidden(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_66,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_176,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_215,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_tops_1(A_91,B_92),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_219,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_215])).

tff(c_225,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_219])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_228,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_229,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [C_67] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | r1_tarski('#skF_7'(C_67),'#skF_3')
      | ~ r2_hidden(C_67,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_181,plain,(
    ! [C_67] :
      ( r1_tarski('#skF_7'(C_67),'#skF_3')
      | ~ r2_hidden(C_67,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_72])).

tff(c_94,plain,(
    ! [C_67] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | v3_pre_topc('#skF_7'(C_67),'#skF_2')
      | ~ r2_hidden(C_67,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_191,plain,(
    ! [C_67] :
      ( v3_pre_topc('#skF_7'(C_67),'#skF_2')
      | ~ r2_hidden(C_67,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_94])).

tff(c_116,plain,(
    ! [C_67] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | m1_subset_1('#skF_7'(C_67),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_67,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_204,plain,(
    ! [C_67] :
      ( m1_subset_1('#skF_7'(C_67),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_67,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_116])).

tff(c_636,plain,(
    ! [B_179,A_180,C_181] :
      ( r1_tarski(B_179,k1_tops_1(A_180,C_181))
      | ~ r1_tarski(B_179,C_181)
      | ~ v3_pre_topc(B_179,A_180)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_640,plain,(
    ! [B_179] :
      ( r1_tarski(B_179,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_179,'#skF_3')
      | ~ v3_pre_topc(B_179,'#skF_2')
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_636])).

tff(c_728,plain,(
    ! [B_189] :
      ( r1_tarski(B_189,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_189,'#skF_3')
      | ~ v3_pre_topc(B_189,'#skF_2')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_640])).

tff(c_740,plain,(
    ! [C_190] :
      ( r1_tarski('#skF_7'(C_190),k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'(C_190),'#skF_3')
      | ~ v3_pre_topc('#skF_7'(C_190),'#skF_2')
      | ~ r2_hidden(C_190,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_204,c_728])).

tff(c_50,plain,(
    ! [C_67] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | r2_hidden(C_67,'#skF_7'(C_67))
      | ~ r2_hidden(C_67,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_187,plain,(
    ! [C_82] :
      ( r2_hidden(C_82,'#skF_7'(C_82))
      | ~ r2_hidden(C_82,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_50])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_190,plain,(
    ! [C_82,B_2] :
      ( r2_hidden(C_82,B_2)
      | ~ r1_tarski('#skF_7'(C_82),B_2)
      | ~ r2_hidden(C_82,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_187,c_2])).

tff(c_764,plain,(
    ! [C_191] :
      ( r2_hidden(C_191,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'(C_191),'#skF_3')
      | ~ v3_pre_topc('#skF_7'(C_191),'#skF_2')
      | ~ r2_hidden(C_191,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_740,c_190])).

tff(c_769,plain,(
    ! [C_192] :
      ( r2_hidden(C_192,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'(C_192),'#skF_3')
      | ~ r2_hidden(C_192,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_191,c_764])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_833,plain,(
    ! [A_202] :
      ( r1_tarski(A_202,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'('#skF_1'(A_202,k1_tops_1('#skF_2','#skF_3'))),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_202,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_769,c_4])).

tff(c_844,plain,(
    ! [A_203] :
      ( r1_tarski(A_203,k1_tops_1('#skF_2','#skF_3'))
      | ~ r2_hidden('#skF_1'(A_203,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_181,c_833])).

tff(c_884,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_844])).

tff(c_905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_229,c_884])).

tff(c_906,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_16,plain,(
    ! [C_23,A_11,D_25,B_19] :
      ( v3_pre_topc(C_23,A_11)
      | k1_tops_1(A_11,C_23) != C_23
      | ~ m1_subset_1(D_25,k1_zfmisc_1(u1_struct_0(B_19)))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(B_19)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1345,plain,(
    ! [D_288,B_289] :
      ( ~ m1_subset_1(D_288,k1_zfmisc_1(u1_struct_0(B_289)))
      | ~ l1_pre_topc(B_289) ) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_1351,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1345])).

tff(c_1358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1351])).

tff(c_1360,plain,(
    ! [C_290,A_291] :
      ( v3_pre_topc(C_290,A_291)
      | k1_tops_1(A_291,C_290) != C_290
      | ~ m1_subset_1(C_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291) ) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_1366,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1360])).

tff(c_1372,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_906,c_1366])).

tff(c_1374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_1372])).

tff(c_1376,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1378,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_42])).

tff(c_1379,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1378])).

tff(c_34,plain,(
    ! [D_66] :
      ( r1_tarski('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_6',D_66)
      | ~ r1_tarski(D_66,'#skF_3')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1521,plain,(
    ! [D_66] :
      ( r1_tarski('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_6',D_66)
      | ~ r1_tarski(D_66,'#skF_3')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_34])).

tff(c_1535,plain,(
    ! [D_324] :
      ( ~ r2_hidden('#skF_6',D_324)
      | ~ r1_tarski(D_324,'#skF_3')
      | ~ v3_pre_topc(D_324,'#skF_2')
      | ~ m1_subset_1(D_324,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_1521])).

tff(c_1538,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1535])).

tff(c_1542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_12,c_1379,c_1538])).

tff(c_1543,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1521])).

tff(c_32,plain,(
    ! [D_66] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r2_hidden('#skF_6',D_66)
      | ~ r1_tarski(D_66,'#skF_3')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1506,plain,(
    ! [D_66] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r2_hidden('#skF_6',D_66)
      | ~ r1_tarski(D_66,'#skF_3')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_32])).

tff(c_1508,plain,(
    ! [D_320] :
      ( ~ r2_hidden('#skF_6',D_320)
      | ~ r1_tarski(D_320,'#skF_3')
      | ~ v3_pre_topc(D_320,'#skF_2')
      | ~ m1_subset_1(D_320,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_1506])).

tff(c_1511,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1508])).

tff(c_1515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_12,c_1379,c_1511])).

tff(c_1516,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1506])).

tff(c_1519,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_4',B_2)
      | ~ r1_tarski('#skF_5',B_2) ) ),
    inference(resolution,[status(thm)],[c_1516,c_2])).

tff(c_30,plain,(
    ! [D_66] :
      ( ~ r2_hidden('#skF_4','#skF_3')
      | ~ r2_hidden('#skF_6',D_66)
      | ~ r1_tarski(D_66,'#skF_3')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1563,plain,(
    ! [D_66] :
      ( ~ r2_hidden('#skF_4','#skF_3')
      | ~ r2_hidden('#skF_6',D_66)
      | ~ r1_tarski(D_66,'#skF_3')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_30])).

tff(c_1564,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1563])).

tff(c_1567,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1519,c_1564])).

tff(c_1571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_1567])).

tff(c_1606,plain,(
    ! [D_331] :
      ( ~ r2_hidden('#skF_6',D_331)
      | ~ r1_tarski(D_331,'#skF_3')
      | ~ v3_pre_topc(D_331,'#skF_2')
      | ~ m1_subset_1(D_331,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_1563])).

tff(c_1609,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1606])).

tff(c_1613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_12,c_1379,c_1609])).

tff(c_1615,plain,(
    ~ r2_hidden('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_44,plain,
    ( r1_tarski('#skF_5','#skF_3')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1621,plain,
    ( r1_tarski('#skF_5','#skF_3')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_44])).

tff(c_1622,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_1621])).

tff(c_1614,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_1627,plain,(
    ! [C_332,B_333,A_334] :
      ( r2_hidden(C_332,B_333)
      | ~ r2_hidden(C_332,A_334)
      | ~ r1_tarski(A_334,B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1634,plain,(
    ! [B_335] :
      ( r2_hidden('#skF_4',B_335)
      | ~ r1_tarski('#skF_5',B_335) ) ),
    inference(resolution,[status(thm)],[c_1614,c_1627])).

tff(c_1375,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1616,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_1375])).

tff(c_1639,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1634,c_1616])).

tff(c_1644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1622,c_1639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.85  
% 4.71/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.85  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.71/1.85  
% 4.71/1.85  %Foreground sorts:
% 4.71/1.85  
% 4.71/1.85  
% 4.71/1.85  %Background operators:
% 4.71/1.85  
% 4.71/1.85  
% 4.71/1.85  %Foreground operators:
% 4.71/1.85  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.71/1.85  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.71/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.71/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.71/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.71/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.71/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.71/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.71/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.71/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.71/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.85  
% 4.96/1.87  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, B)) & r2_hidden(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_1)).
% 4.96/1.87  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.96/1.87  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.96/1.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.96/1.87  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 4.96/1.87  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 4.96/1.87  tff(c_40, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_176, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 4.96/1.87  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_215, plain, (![A_91, B_92]: (r1_tarski(k1_tops_1(A_91, B_92), B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.96/1.87  tff(c_219, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_215])).
% 4.96/1.87  tff(c_225, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_219])).
% 4.96/1.87  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.96/1.87  tff(c_228, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_225, c_8])).
% 4.96/1.87  tff(c_229, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_228])).
% 4.96/1.87  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.96/1.87  tff(c_72, plain, (![C_67]: (v3_pre_topc('#skF_3', '#skF_2') | r1_tarski('#skF_7'(C_67), '#skF_3') | ~r2_hidden(C_67, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_181, plain, (![C_67]: (r1_tarski('#skF_7'(C_67), '#skF_3') | ~r2_hidden(C_67, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_176, c_72])).
% 4.96/1.87  tff(c_94, plain, (![C_67]: (v3_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_7'(C_67), '#skF_2') | ~r2_hidden(C_67, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_191, plain, (![C_67]: (v3_pre_topc('#skF_7'(C_67), '#skF_2') | ~r2_hidden(C_67, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_176, c_94])).
% 4.96/1.87  tff(c_116, plain, (![C_67]: (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1('#skF_7'(C_67), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_67, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_204, plain, (![C_67]: (m1_subset_1('#skF_7'(C_67), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_67, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_176, c_116])).
% 4.96/1.87  tff(c_636, plain, (![B_179, A_180, C_181]: (r1_tarski(B_179, k1_tops_1(A_180, C_181)) | ~r1_tarski(B_179, C_181) | ~v3_pre_topc(B_179, A_180) | ~m1_subset_1(C_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.96/1.87  tff(c_640, plain, (![B_179]: (r1_tarski(B_179, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_179, '#skF_3') | ~v3_pre_topc(B_179, '#skF_2') | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_636])).
% 4.96/1.87  tff(c_728, plain, (![B_189]: (r1_tarski(B_189, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_189, '#skF_3') | ~v3_pre_topc(B_189, '#skF_2') | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_640])).
% 4.96/1.87  tff(c_740, plain, (![C_190]: (r1_tarski('#skF_7'(C_190), k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'(C_190), '#skF_3') | ~v3_pre_topc('#skF_7'(C_190), '#skF_2') | ~r2_hidden(C_190, '#skF_3'))), inference(resolution, [status(thm)], [c_204, c_728])).
% 4.96/1.87  tff(c_50, plain, (![C_67]: (v3_pre_topc('#skF_3', '#skF_2') | r2_hidden(C_67, '#skF_7'(C_67)) | ~r2_hidden(C_67, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_187, plain, (![C_82]: (r2_hidden(C_82, '#skF_7'(C_82)) | ~r2_hidden(C_82, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_176, c_50])).
% 4.96/1.87  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.96/1.87  tff(c_190, plain, (![C_82, B_2]: (r2_hidden(C_82, B_2) | ~r1_tarski('#skF_7'(C_82), B_2) | ~r2_hidden(C_82, '#skF_3'))), inference(resolution, [status(thm)], [c_187, c_2])).
% 4.96/1.87  tff(c_764, plain, (![C_191]: (r2_hidden(C_191, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'(C_191), '#skF_3') | ~v3_pre_topc('#skF_7'(C_191), '#skF_2') | ~r2_hidden(C_191, '#skF_3'))), inference(resolution, [status(thm)], [c_740, c_190])).
% 4.96/1.87  tff(c_769, plain, (![C_192]: (r2_hidden(C_192, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'(C_192), '#skF_3') | ~r2_hidden(C_192, '#skF_3'))), inference(resolution, [status(thm)], [c_191, c_764])).
% 4.96/1.87  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.96/1.87  tff(c_833, plain, (![A_202]: (r1_tarski(A_202, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'('#skF_1'(A_202, k1_tops_1('#skF_2', '#skF_3'))), '#skF_3') | ~r2_hidden('#skF_1'(A_202, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_769, c_4])).
% 4.96/1.87  tff(c_844, plain, (![A_203]: (r1_tarski(A_203, k1_tops_1('#skF_2', '#skF_3')) | ~r2_hidden('#skF_1'(A_203, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_181, c_833])).
% 4.96/1.87  tff(c_884, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_844])).
% 4.96/1.87  tff(c_905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_229, c_884])).
% 4.96/1.87  tff(c_906, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_228])).
% 4.96/1.87  tff(c_16, plain, (![C_23, A_11, D_25, B_19]: (v3_pre_topc(C_23, A_11) | k1_tops_1(A_11, C_23)!=C_23 | ~m1_subset_1(D_25, k1_zfmisc_1(u1_struct_0(B_19))) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(B_19) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.96/1.87  tff(c_1345, plain, (![D_288, B_289]: (~m1_subset_1(D_288, k1_zfmisc_1(u1_struct_0(B_289))) | ~l1_pre_topc(B_289))), inference(splitLeft, [status(thm)], [c_16])).
% 4.96/1.87  tff(c_1351, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1345])).
% 4.96/1.87  tff(c_1358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1351])).
% 4.96/1.87  tff(c_1360, plain, (![C_290, A_291]: (v3_pre_topc(C_290, A_291) | k1_tops_1(A_291, C_290)!=C_290 | ~m1_subset_1(C_290, k1_zfmisc_1(u1_struct_0(A_291))) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291))), inference(splitRight, [status(thm)], [c_16])).
% 4.96/1.87  tff(c_1366, plain, (v3_pre_topc('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1360])).
% 4.96/1.87  tff(c_1372, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_906, c_1366])).
% 4.96/1.87  tff(c_1374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_1372])).
% 4.96/1.87  tff(c_1376, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.96/1.87  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.96/1.87  tff(c_42, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_1378, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_42])).
% 4.96/1.87  tff(c_1379, plain, (r2_hidden('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_1378])).
% 4.96/1.87  tff(c_34, plain, (![D_66]: (r1_tarski('#skF_5', '#skF_3') | ~r2_hidden('#skF_6', D_66) | ~r1_tarski(D_66, '#skF_3') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_1521, plain, (![D_66]: (r1_tarski('#skF_5', '#skF_3') | ~r2_hidden('#skF_6', D_66) | ~r1_tarski(D_66, '#skF_3') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_34])).
% 4.96/1.87  tff(c_1535, plain, (![D_324]: (~r2_hidden('#skF_6', D_324) | ~r1_tarski(D_324, '#skF_3') | ~v3_pre_topc(D_324, '#skF_2') | ~m1_subset_1(D_324, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1521])).
% 4.96/1.87  tff(c_1538, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_1535])).
% 4.96/1.87  tff(c_1542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1376, c_12, c_1379, c_1538])).
% 4.96/1.87  tff(c_1543, plain, (r1_tarski('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_1521])).
% 4.96/1.87  tff(c_32, plain, (![D_66]: (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_6', D_66) | ~r1_tarski(D_66, '#skF_3') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_1506, plain, (![D_66]: (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_6', D_66) | ~r1_tarski(D_66, '#skF_3') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_32])).
% 4.96/1.87  tff(c_1508, plain, (![D_320]: (~r2_hidden('#skF_6', D_320) | ~r1_tarski(D_320, '#skF_3') | ~v3_pre_topc(D_320, '#skF_2') | ~m1_subset_1(D_320, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1506])).
% 4.96/1.87  tff(c_1511, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_1508])).
% 4.96/1.87  tff(c_1515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1376, c_12, c_1379, c_1511])).
% 4.96/1.87  tff(c_1516, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1506])).
% 4.96/1.87  tff(c_1519, plain, (![B_2]: (r2_hidden('#skF_4', B_2) | ~r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_1516, c_2])).
% 4.96/1.87  tff(c_30, plain, (![D_66]: (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_6', D_66) | ~r1_tarski(D_66, '#skF_3') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_1563, plain, (![D_66]: (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_6', D_66) | ~r1_tarski(D_66, '#skF_3') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_30])).
% 4.96/1.87  tff(c_1564, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1563])).
% 4.96/1.87  tff(c_1567, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1519, c_1564])).
% 4.96/1.87  tff(c_1571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1543, c_1567])).
% 4.96/1.87  tff(c_1606, plain, (![D_331]: (~r2_hidden('#skF_6', D_331) | ~r1_tarski(D_331, '#skF_3') | ~v3_pre_topc(D_331, '#skF_2') | ~m1_subset_1(D_331, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1563])).
% 4.96/1.87  tff(c_1609, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_1606])).
% 4.96/1.87  tff(c_1613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1376, c_12, c_1379, c_1609])).
% 4.96/1.87  tff(c_1615, plain, (~r2_hidden('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_1378])).
% 4.96/1.87  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_3') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.96/1.87  tff(c_1621, plain, (r1_tarski('#skF_5', '#skF_3') | r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_44])).
% 4.96/1.87  tff(c_1622, plain, (r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1615, c_1621])).
% 4.96/1.87  tff(c_1614, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1378])).
% 4.96/1.87  tff(c_1627, plain, (![C_332, B_333, A_334]: (r2_hidden(C_332, B_333) | ~r2_hidden(C_332, A_334) | ~r1_tarski(A_334, B_333))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.96/1.87  tff(c_1634, plain, (![B_335]: (r2_hidden('#skF_4', B_335) | ~r1_tarski('#skF_5', B_335))), inference(resolution, [status(thm)], [c_1614, c_1627])).
% 4.96/1.87  tff(c_1375, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 4.96/1.87  tff(c_1616, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1615, c_1375])).
% 4.96/1.87  tff(c_1639, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1634, c_1616])).
% 4.96/1.87  tff(c_1644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1622, c_1639])).
% 4.96/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.87  
% 4.96/1.87  Inference rules
% 4.96/1.87  ----------------------
% 4.96/1.87  #Ref     : 0
% 4.96/1.87  #Sup     : 319
% 4.96/1.87  #Fact    : 0
% 4.96/1.87  #Define  : 0
% 4.96/1.87  #Split   : 15
% 4.96/1.87  #Chain   : 0
% 4.96/1.87  #Close   : 0
% 4.96/1.87  
% 4.96/1.87  Ordering : KBO
% 4.96/1.87  
% 4.96/1.87  Simplification rules
% 4.96/1.87  ----------------------
% 4.96/1.87  #Subsume      : 199
% 4.96/1.87  #Demod        : 107
% 4.96/1.87  #Tautology    : 63
% 4.96/1.87  #SimpNegUnit  : 12
% 4.96/1.87  #BackRed      : 1
% 4.96/1.87  
% 4.96/1.87  #Partial instantiations: 0
% 4.96/1.87  #Strategies tried      : 1
% 4.96/1.87  
% 4.96/1.87  Timing (in seconds)
% 4.96/1.87  ----------------------
% 4.96/1.87  Preprocessing        : 0.35
% 4.96/1.87  Parsing              : 0.17
% 4.96/1.87  CNF conversion       : 0.03
% 4.96/1.87  Main loop            : 0.69
% 4.96/1.87  Inferencing          : 0.20
% 4.96/1.87  Reduction            : 0.16
% 4.96/1.87  Demodulation         : 0.10
% 4.96/1.87  BG Simplification    : 0.04
% 4.96/1.87  Subsumption          : 0.24
% 4.96/1.87  Abstraction          : 0.03
% 4.96/1.87  MUC search           : 0.00
% 4.96/1.87  Cooper               : 0.00
% 4.96/1.87  Total                : 1.07
% 4.96/1.87  Index Insertion      : 0.00
% 4.96/1.87  Index Deletion       : 0.00
% 4.96/1.87  Index Matching       : 0.00
% 4.96/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
