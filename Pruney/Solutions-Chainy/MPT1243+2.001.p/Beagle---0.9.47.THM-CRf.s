%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:49 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 242 expanded)
%              Number of leaves         :   26 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 ( 883 expanded)
%              Number of equality atoms :    4 (  13 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_8 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
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

tff(f_53,axiom,(
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

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(c_52,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | r2_hidden('#skF_7','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_182,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_221,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k1_tops_1(A_83,B_84),B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_225,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_221])).

tff(c_231,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_225])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_234,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_231,c_8])).

tff(c_235,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [C_59] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | r1_tarski('#skF_8'(C_59),'#skF_4')
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_187,plain,(
    ! [C_59] :
      ( r1_tarski('#skF_8'(C_59),'#skF_4')
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_78])).

tff(c_100,plain,(
    ! [C_59] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | v3_pre_topc('#skF_8'(C_59),'#skF_3')
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_197,plain,(
    ! [C_59] :
      ( v3_pre_topc('#skF_8'(C_59),'#skF_3')
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_100])).

tff(c_122,plain,(
    ! [C_59] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | m1_subset_1('#skF_8'(C_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_210,plain,(
    ! [C_59] :
      ( m1_subset_1('#skF_8'(C_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_122])).

tff(c_56,plain,(
    ! [C_59] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | r2_hidden(C_59,'#skF_8'(C_59))
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_192,plain,(
    ! [C_59] :
      ( r2_hidden(C_59,'#skF_8'(C_59))
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_56])).

tff(c_957,plain,(
    ! [B_239,A_240,C_241,D_242] :
      ( r2_hidden(B_239,k1_tops_1(A_240,C_241))
      | ~ r2_hidden(B_239,D_242)
      | ~ r1_tarski(D_242,C_241)
      | ~ v3_pre_topc(D_242,A_240)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ m1_subset_1(C_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1025,plain,(
    ! [C_250,A_251,C_252] :
      ( r2_hidden(C_250,k1_tops_1(A_251,C_252))
      | ~ r1_tarski('#skF_8'(C_250),C_252)
      | ~ v3_pre_topc('#skF_8'(C_250),A_251)
      | ~ m1_subset_1('#skF_8'(C_250),k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ m1_subset_1(C_252,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | ~ r2_hidden(C_250,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_192,c_957])).

tff(c_1027,plain,(
    ! [C_59,C_252] :
      ( r2_hidden(C_59,k1_tops_1('#skF_3',C_252))
      | ~ r1_tarski('#skF_8'(C_59),C_252)
      | ~ v3_pre_topc('#skF_8'(C_59),'#skF_3')
      | ~ m1_subset_1(C_252,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r2_hidden(C_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_210,c_1025])).

tff(c_1031,plain,(
    ! [C_253,C_254] :
      ( r2_hidden(C_253,k1_tops_1('#skF_3',C_254))
      | ~ r1_tarski('#skF_8'(C_253),C_254)
      | ~ v3_pre_topc('#skF_8'(C_253),'#skF_3')
      | ~ m1_subset_1(C_254,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_253,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1027])).

tff(c_1035,plain,(
    ! [C_255,C_256] :
      ( r2_hidden(C_255,k1_tops_1('#skF_3',C_256))
      | ~ r1_tarski('#skF_8'(C_255),C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_255,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_197,c_1031])).

tff(c_1048,plain,(
    ! [C_257] :
      ( r2_hidden(C_257,k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_8'(C_257),'#skF_4')
      | ~ r2_hidden(C_257,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_1035])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1196,plain,(
    ! [A_277] :
      ( r1_tarski(A_277,k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_8'('#skF_1'(A_277,k1_tops_1('#skF_3','#skF_4'))),'#skF_4')
      | ~ r2_hidden('#skF_1'(A_277,k1_tops_1('#skF_3','#skF_4')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1048,c_4])).

tff(c_1221,plain,(
    ! [A_281] :
      ( r1_tarski(A_281,k1_tops_1('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_281,k1_tops_1('#skF_3','#skF_4')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_187,c_1196])).

tff(c_1257,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1221])).

tff(c_1275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_235,c_1257])).

tff(c_1276,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_1289,plain,(
    ! [A_283,B_284] :
      ( v3_pre_topc(k1_tops_1(A_283,B_284),A_283)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1293,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1289])).

tff(c_1299,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1276,c_1293])).

tff(c_1301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1299])).

tff(c_1303,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | r2_hidden('#skF_7','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1306,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_50])).

tff(c_1307,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1306])).

tff(c_38,plain,(
    ! [D_58] :
      ( r2_hidden('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',D_58)
      | ~ r1_tarski(D_58,'#skF_4')
      | ~ v3_pre_topc(D_58,'#skF_3')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1473,plain,(
    ! [D_58] :
      ( r2_hidden('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',D_58)
      | ~ r1_tarski(D_58,'#skF_4')
      | ~ v3_pre_topc(D_58,'#skF_3')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_38])).

tff(c_1478,plain,(
    ! [D_324] :
      ( ~ r2_hidden('#skF_7',D_324)
      | ~ r1_tarski(D_324,'#skF_4')
      | ~ v3_pre_topc(D_324,'#skF_3')
      | ~ m1_subset_1(D_324,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitLeft,[status(thm)],[c_1473])).

tff(c_1481,plain,
    ( ~ r2_hidden('#skF_7','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1478])).

tff(c_1485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_12,c_1307,c_1481])).

tff(c_1486,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1473])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1490,plain,(
    ! [B_325] :
      ( r2_hidden('#skF_5',B_325)
      | ~ r1_tarski('#skF_6',B_325) ) ),
    inference(resolution,[status(thm)],[c_1486,c_2])).

tff(c_36,plain,(
    ! [D_58] :
      ( ~ r2_hidden('#skF_5','#skF_4')
      | ~ r2_hidden('#skF_7',D_58)
      | ~ r1_tarski(D_58,'#skF_4')
      | ~ v3_pre_topc(D_58,'#skF_3')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1444,plain,(
    ! [D_58] :
      ( ~ r2_hidden('#skF_5','#skF_4')
      | ~ r2_hidden('#skF_7',D_58)
      | ~ r1_tarski(D_58,'#skF_4')
      | ~ v3_pre_topc(D_58,'#skF_3')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_36])).

tff(c_1445,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1444])).

tff(c_1503,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1490,c_1445])).

tff(c_40,plain,(
    ! [D_58] :
      ( r1_tarski('#skF_6','#skF_4')
      | ~ r2_hidden('#skF_7',D_58)
      | ~ r1_tarski(D_58,'#skF_4')
      | ~ v3_pre_topc(D_58,'#skF_3')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1516,plain,(
    ! [D_58] :
      ( r1_tarski('#skF_6','#skF_4')
      | ~ r2_hidden('#skF_7',D_58)
      | ~ r1_tarski(D_58,'#skF_4')
      | ~ v3_pre_topc(D_58,'#skF_3')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_40])).

tff(c_1518,plain,(
    ! [D_328] :
      ( ~ r2_hidden('#skF_7',D_328)
      | ~ r1_tarski(D_328,'#skF_4')
      | ~ v3_pre_topc(D_328,'#skF_3')
      | ~ m1_subset_1(D_328,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1503,c_1516])).

tff(c_1521,plain,
    ( ~ r2_hidden('#skF_7','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1518])).

tff(c_1525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_12,c_1307,c_1521])).

tff(c_1549,plain,(
    ! [D_332] :
      ( ~ r2_hidden('#skF_7',D_332)
      | ~ r1_tarski(D_332,'#skF_4')
      | ~ v3_pre_topc(D_332,'#skF_3')
      | ~ m1_subset_1(D_332,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_1444])).

tff(c_1552,plain,
    ( ~ r2_hidden('#skF_7','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1549])).

tff(c_1556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_12,c_1307,c_1552])).

tff(c_1557,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1306])).

tff(c_1558,plain,(
    ~ r2_hidden('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1306])).

tff(c_48,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1564,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_48])).

tff(c_1565,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1558,c_1564])).

tff(c_1566,plain,(
    ! [C_333,B_334,A_335] :
      ( r2_hidden(C_333,B_334)
      | ~ r2_hidden(C_333,A_335)
      | ~ r1_tarski(A_335,B_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1571,plain,(
    ! [B_334] :
      ( r2_hidden('#skF_5',B_334)
      | ~ r1_tarski('#skF_6',B_334) ) ),
    inference(resolution,[status(thm)],[c_1565,c_1566])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1578,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_46])).

tff(c_1579,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1558,c_1578])).

tff(c_1582,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1571,c_1579])).

tff(c_1586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.74  
% 7.49/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.75  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_8 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 7.49/2.75  
% 7.49/2.75  %Foreground sorts:
% 7.49/2.75  
% 7.49/2.75  
% 7.49/2.75  %Background operators:
% 7.49/2.75  
% 7.49/2.75  
% 7.49/2.75  %Foreground operators:
% 7.49/2.75  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.49/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.49/2.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.49/2.75  tff('#skF_8', type, '#skF_8': $i > $i).
% 7.49/2.75  tff('#skF_7', type, '#skF_7': $i).
% 7.49/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.49/2.75  tff('#skF_5', type, '#skF_5': $i).
% 7.49/2.75  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.49/2.75  tff('#skF_6', type, '#skF_6': $i).
% 7.49/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.49/2.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.49/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.49/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.49/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.49/2.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.49/2.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.49/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.49/2.75  
% 7.49/2.77  tff(f_93, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, B)) & r2_hidden(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_1)).
% 7.49/2.77  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 7.49/2.77  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.49/2.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.49/2.77  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 7.49/2.77  tff(f_46, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 7.49/2.77  tff(c_52, plain, (v3_pre_topc('#skF_6', '#skF_3') | r2_hidden('#skF_7', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_182, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 7.49/2.77  tff(c_32, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_221, plain, (![A_83, B_84]: (r1_tarski(k1_tops_1(A_83, B_84), B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.49/2.77  tff(c_225, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_221])).
% 7.49/2.77  tff(c_231, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_225])).
% 7.49/2.77  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.49/2.77  tff(c_234, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_231, c_8])).
% 7.49/2.77  tff(c_235, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_234])).
% 7.49/2.77  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.49/2.77  tff(c_78, plain, (![C_59]: (v3_pre_topc('#skF_4', '#skF_3') | r1_tarski('#skF_8'(C_59), '#skF_4') | ~r2_hidden(C_59, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_187, plain, (![C_59]: (r1_tarski('#skF_8'(C_59), '#skF_4') | ~r2_hidden(C_59, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_182, c_78])).
% 7.49/2.77  tff(c_100, plain, (![C_59]: (v3_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_8'(C_59), '#skF_3') | ~r2_hidden(C_59, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_197, plain, (![C_59]: (v3_pre_topc('#skF_8'(C_59), '#skF_3') | ~r2_hidden(C_59, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_182, c_100])).
% 7.49/2.77  tff(c_122, plain, (![C_59]: (v3_pre_topc('#skF_4', '#skF_3') | m1_subset_1('#skF_8'(C_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_59, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_210, plain, (![C_59]: (m1_subset_1('#skF_8'(C_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_59, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_182, c_122])).
% 7.49/2.77  tff(c_56, plain, (![C_59]: (v3_pre_topc('#skF_4', '#skF_3') | r2_hidden(C_59, '#skF_8'(C_59)) | ~r2_hidden(C_59, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_192, plain, (![C_59]: (r2_hidden(C_59, '#skF_8'(C_59)) | ~r2_hidden(C_59, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_182, c_56])).
% 7.49/2.77  tff(c_957, plain, (![B_239, A_240, C_241, D_242]: (r2_hidden(B_239, k1_tops_1(A_240, C_241)) | ~r2_hidden(B_239, D_242) | ~r1_tarski(D_242, C_241) | ~v3_pre_topc(D_242, A_240) | ~m1_subset_1(D_242, k1_zfmisc_1(u1_struct_0(A_240))) | ~m1_subset_1(C_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.49/2.77  tff(c_1025, plain, (![C_250, A_251, C_252]: (r2_hidden(C_250, k1_tops_1(A_251, C_252)) | ~r1_tarski('#skF_8'(C_250), C_252) | ~v3_pre_topc('#skF_8'(C_250), A_251) | ~m1_subset_1('#skF_8'(C_250), k1_zfmisc_1(u1_struct_0(A_251))) | ~m1_subset_1(C_252, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | ~r2_hidden(C_250, '#skF_4'))), inference(resolution, [status(thm)], [c_192, c_957])).
% 7.49/2.77  tff(c_1027, plain, (![C_59, C_252]: (r2_hidden(C_59, k1_tops_1('#skF_3', C_252)) | ~r1_tarski('#skF_8'(C_59), C_252) | ~v3_pre_topc('#skF_8'(C_59), '#skF_3') | ~m1_subset_1(C_252, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden(C_59, '#skF_4'))), inference(resolution, [status(thm)], [c_210, c_1025])).
% 7.49/2.77  tff(c_1031, plain, (![C_253, C_254]: (r2_hidden(C_253, k1_tops_1('#skF_3', C_254)) | ~r1_tarski('#skF_8'(C_253), C_254) | ~v3_pre_topc('#skF_8'(C_253), '#skF_3') | ~m1_subset_1(C_254, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_253, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1027])).
% 7.49/2.77  tff(c_1035, plain, (![C_255, C_256]: (r2_hidden(C_255, k1_tops_1('#skF_3', C_256)) | ~r1_tarski('#skF_8'(C_255), C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_255, '#skF_4'))), inference(resolution, [status(thm)], [c_197, c_1031])).
% 7.49/2.77  tff(c_1048, plain, (![C_257]: (r2_hidden(C_257, k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_8'(C_257), '#skF_4') | ~r2_hidden(C_257, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_1035])).
% 7.49/2.77  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.49/2.77  tff(c_1196, plain, (![A_277]: (r1_tarski(A_277, k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_8'('#skF_1'(A_277, k1_tops_1('#skF_3', '#skF_4'))), '#skF_4') | ~r2_hidden('#skF_1'(A_277, k1_tops_1('#skF_3', '#skF_4')), '#skF_4'))), inference(resolution, [status(thm)], [c_1048, c_4])).
% 7.49/2.77  tff(c_1221, plain, (![A_281]: (r1_tarski(A_281, k1_tops_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_281, k1_tops_1('#skF_3', '#skF_4')), '#skF_4'))), inference(resolution, [status(thm)], [c_187, c_1196])).
% 7.49/2.77  tff(c_1257, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1221])).
% 7.49/2.77  tff(c_1275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_235, c_1257])).
% 7.49/2.77  tff(c_1276, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_234])).
% 7.49/2.77  tff(c_1289, plain, (![A_283, B_284]: (v3_pre_topc(k1_tops_1(A_283, B_284), A_283) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0(A_283))) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.49/2.77  tff(c_1293, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1289])).
% 7.49/2.77  tff(c_1299, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1276, c_1293])).
% 7.49/2.77  tff(c_1301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_1299])).
% 7.49/2.77  tff(c_1303, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 7.49/2.77  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.49/2.77  tff(c_50, plain, (r1_tarski('#skF_6', '#skF_4') | r2_hidden('#skF_7', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_1306, plain, (r1_tarski('#skF_6', '#skF_4') | r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_50])).
% 7.49/2.77  tff(c_1307, plain, (r2_hidden('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_1306])).
% 7.49/2.77  tff(c_38, plain, (![D_58]: (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', D_58) | ~r1_tarski(D_58, '#skF_4') | ~v3_pre_topc(D_58, '#skF_3') | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_1473, plain, (![D_58]: (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', D_58) | ~r1_tarski(D_58, '#skF_4') | ~v3_pre_topc(D_58, '#skF_3') | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_38])).
% 7.49/2.77  tff(c_1478, plain, (![D_324]: (~r2_hidden('#skF_7', D_324) | ~r1_tarski(D_324, '#skF_4') | ~v3_pre_topc(D_324, '#skF_3') | ~m1_subset_1(D_324, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_1473])).
% 7.49/2.77  tff(c_1481, plain, (~r2_hidden('#skF_7', '#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_1478])).
% 7.49/2.77  tff(c_1485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1303, c_12, c_1307, c_1481])).
% 7.49/2.77  tff(c_1486, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1473])).
% 7.49/2.77  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.49/2.77  tff(c_1490, plain, (![B_325]: (r2_hidden('#skF_5', B_325) | ~r1_tarski('#skF_6', B_325))), inference(resolution, [status(thm)], [c_1486, c_2])).
% 7.49/2.77  tff(c_36, plain, (![D_58]: (~r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_7', D_58) | ~r1_tarski(D_58, '#skF_4') | ~v3_pre_topc(D_58, '#skF_3') | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_1444, plain, (![D_58]: (~r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_7', D_58) | ~r1_tarski(D_58, '#skF_4') | ~v3_pre_topc(D_58, '#skF_3') | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_36])).
% 7.49/2.77  tff(c_1445, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1444])).
% 7.49/2.77  tff(c_1503, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1490, c_1445])).
% 7.49/2.77  tff(c_40, plain, (![D_58]: (r1_tarski('#skF_6', '#skF_4') | ~r2_hidden('#skF_7', D_58) | ~r1_tarski(D_58, '#skF_4') | ~v3_pre_topc(D_58, '#skF_3') | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_1516, plain, (![D_58]: (r1_tarski('#skF_6', '#skF_4') | ~r2_hidden('#skF_7', D_58) | ~r1_tarski(D_58, '#skF_4') | ~v3_pre_topc(D_58, '#skF_3') | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_40])).
% 7.49/2.77  tff(c_1518, plain, (![D_328]: (~r2_hidden('#skF_7', D_328) | ~r1_tarski(D_328, '#skF_4') | ~v3_pre_topc(D_328, '#skF_3') | ~m1_subset_1(D_328, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_1503, c_1516])).
% 7.49/2.77  tff(c_1521, plain, (~r2_hidden('#skF_7', '#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_1518])).
% 7.49/2.77  tff(c_1525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1303, c_12, c_1307, c_1521])).
% 7.49/2.77  tff(c_1549, plain, (![D_332]: (~r2_hidden('#skF_7', D_332) | ~r1_tarski(D_332, '#skF_4') | ~v3_pre_topc(D_332, '#skF_3') | ~m1_subset_1(D_332, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_1444])).
% 7.49/2.77  tff(c_1552, plain, (~r2_hidden('#skF_7', '#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_1549])).
% 7.49/2.77  tff(c_1556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1303, c_12, c_1307, c_1552])).
% 7.49/2.77  tff(c_1557, plain, (r1_tarski('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_1306])).
% 7.49/2.77  tff(c_1558, plain, (~r2_hidden('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_1306])).
% 7.49/2.77  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_7', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_1564, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_48])).
% 7.49/2.77  tff(c_1565, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1558, c_1564])).
% 7.49/2.77  tff(c_1566, plain, (![C_333, B_334, A_335]: (r2_hidden(C_333, B_334) | ~r2_hidden(C_333, A_335) | ~r1_tarski(A_335, B_334))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.49/2.77  tff(c_1571, plain, (![B_334]: (r2_hidden('#skF_5', B_334) | ~r1_tarski('#skF_6', B_334))), inference(resolution, [status(thm)], [c_1565, c_1566])).
% 7.49/2.77  tff(c_46, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.77  tff(c_1578, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_46])).
% 7.49/2.77  tff(c_1579, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1558, c_1578])).
% 7.49/2.77  tff(c_1582, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1571, c_1579])).
% 7.49/2.77  tff(c_1586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1582])).
% 7.49/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.77  
% 7.49/2.77  Inference rules
% 7.49/2.77  ----------------------
% 7.49/2.77  #Ref     : 0
% 7.49/2.77  #Sup     : 317
% 7.49/2.77  #Fact    : 0
% 7.49/2.77  #Define  : 0
% 7.49/2.77  #Split   : 9
% 7.49/2.77  #Chain   : 0
% 7.49/2.77  #Close   : 0
% 7.49/2.77  
% 7.49/2.78  Ordering : KBO
% 7.49/2.78  
% 7.49/2.78  Simplification rules
% 7.49/2.78  ----------------------
% 7.49/2.78  #Subsume      : 164
% 7.49/2.78  #Demod        : 118
% 7.49/2.78  #Tautology    : 48
% 7.49/2.78  #SimpNegUnit  : 10
% 7.49/2.78  #BackRed      : 1
% 7.49/2.78  
% 7.49/2.78  #Partial instantiations: 0
% 7.49/2.78  #Strategies tried      : 1
% 7.49/2.78  
% 7.49/2.78  Timing (in seconds)
% 7.49/2.78  ----------------------
% 7.49/2.78  Preprocessing        : 0.54
% 7.49/2.78  Parsing              : 0.24
% 7.49/2.78  CNF conversion       : 0.05
% 7.49/2.78  Main loop            : 1.28
% 7.49/2.78  Inferencing          : 0.39
% 7.49/2.78  Reduction            : 0.31
% 7.49/2.78  Demodulation         : 0.20
% 7.49/2.78  BG Simplification    : 0.06
% 7.49/2.78  Subsumption          : 0.44
% 7.49/2.78  Abstraction          : 0.04
% 7.49/2.78  MUC search           : 0.00
% 7.49/2.78  Cooper               : 0.00
% 7.49/2.78  Total                : 1.88
% 7.49/2.78  Index Insertion      : 0.00
% 7.49/2.78  Index Deletion       : 0.00
% 7.49/2.78  Index Matching       : 0.00
% 7.49/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
