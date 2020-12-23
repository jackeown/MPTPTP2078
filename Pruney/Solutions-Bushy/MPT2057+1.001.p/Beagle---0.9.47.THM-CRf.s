%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2057+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:49 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 551 expanded)
%              Number of leaves         :   37 ( 215 expanded)
%              Depth                    :   16
%              Number of atoms          :  348 (2602 expanded)
%              Number of equality atoms :   20 (  55 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > v6_waybel_0 > v2_waybel_0 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
               => ( r2_hidden(C,B)
                <=> r1_waybel_0(A,k3_yellow19(A,k2_struct_0(A),B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow19)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & v2_waybel_0(C,k3_yellow_1(B))
        & v13_waybel_0(C,k3_yellow_1(B))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B)))) )
     => ( ~ v2_struct_0(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A)
        & l1_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_hidden(C,k2_yellow19(A,B))
            <=> ( r1_waybel_0(A,B,C)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_56,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_48,plain,
    ( ~ r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4,plain,(
    ! [A_1] :
      ( m1_subset_1(k2_struct_0(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_153,plain,(
    ! [A_58,B_59,C_60] :
      ( v6_waybel_0(k3_yellow19(A_58,B_59,C_60),A_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_59))))
      | ~ v13_waybel_0(C_60,k3_yellow_1(B_59))
      | ~ v2_waybel_0(C_60,k3_yellow_1(B_59))
      | v1_xboole_0(C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(B_59)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_158,plain,(
    ! [A_58] :
      ( v6_waybel_0(k3_yellow19(A_58,k2_struct_0('#skF_1'),'#skF_2'),A_58)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_36,c_153])).

tff(c_162,plain,(
    ! [A_58] :
      ( v6_waybel_0(k3_yellow19(A_58,k2_struct_0('#skF_1'),'#skF_2'),A_58)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_158])).

tff(c_163,plain,(
    ! [A_58] :
      ( v6_waybel_0(k3_yellow19(A_58,k2_struct_0('#skF_1'),'#skF_2'),A_58)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_162])).

tff(c_164,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_14,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k2_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_164,c_14])).

tff(c_170,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_167])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_170])).

tff(c_174,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_183,plain,(
    ! [A_62,B_63,C_64] :
      ( l1_waybel_0(k3_yellow19(A_62,B_63,C_64),A_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_63))))
      | ~ v13_waybel_0(C_64,k3_yellow_1(B_63))
      | ~ v2_waybel_0(C_64,k3_yellow_1(B_63))
      | v1_xboole_0(C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(B_63)
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_188,plain,(
    ! [A_62] :
      ( l1_waybel_0(k3_yellow19(A_62,k2_struct_0('#skF_1'),'#skF_2'),A_62)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_36,c_183])).

tff(c_192,plain,(
    ! [A_62] :
      ( l1_waybel_0(k3_yellow19(A_62,k2_struct_0('#skF_1'),'#skF_2'),A_62)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_188])).

tff(c_194,plain,(
    ! [A_65] :
      ( l1_waybel_0(k3_yellow19(A_65,k2_struct_0('#skF_1'),'#skF_2'),A_65)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_42,c_192])).

tff(c_197,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_200,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_197])).

tff(c_201,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_200])).

tff(c_54,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_65,plain,(
    r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_54])).

tff(c_77,plain,(
    ! [A_36,B_37,C_38] :
      ( k7_subset_1(A_36,B_37,C_38) = k4_xboole_0(B_37,C_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [C_38] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_38) = k4_xboole_0('#skF_2',C_38) ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_202,plain,(
    ! [A_66,B_67] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_66))),B_67,k1_tarski(k1_xboole_0)) = k2_yellow19(A_66,k3_yellow19(A_66,k2_struct_0(A_66),B_67))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_66)))))
      | ~ v13_waybel_0(B_67,k3_yellow_1(k2_struct_0(A_66)))
      | ~ v2_waybel_0(B_67,k3_yellow_1(k2_struct_0(A_66)))
      | v1_xboole_0(B_67)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_207,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_202])).

tff(c_211,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_85,c_207])).

tff(c_212,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_211])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_116,plain,(
    ! [C_49,A_50,B_51] :
      ( r2_hidden(C_49,k2_yellow19(A_50,B_51))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ r1_waybel_0(A_50,B_51,C_49)
      | ~ l1_waybel_0(B_51,A_50)
      | v2_struct_0(B_51)
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_122,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_1',B_51))
      | ~ r1_waybel_0('#skF_1',B_51,'#skF_3')
      | ~ l1_waybel_0(B_51,'#skF_1')
      | v2_struct_0(B_51)
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_127,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_1',B_51))
      | ~ r1_waybel_0('#skF_1',B_51,'#skF_3')
      | ~ l1_waybel_0(B_51,'#skF_1')
      | v2_struct_0(B_51)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_122])).

tff(c_128,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_1',B_51))
      | ~ r1_waybel_0('#skF_1',B_51,'#skF_3')
      | ~ l1_waybel_0(B_51,'#skF_1')
      | v2_struct_0(B_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_127])).

tff(c_219,plain,
    ( r2_hidden('#skF_3',k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
    | ~ r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_128])).

tff(c_231,plain,
    ( r2_hidden('#skF_3',k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
    | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_65,c_219])).

tff(c_239,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_10,plain,(
    ! [A_2,B_3,C_4] :
      ( ~ v2_struct_0(k3_yellow19(A_2,B_3,C_4))
      | ~ m1_subset_1(C_4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_3))))
      | ~ v13_waybel_0(C_4,k3_yellow_1(B_3))
      | ~ v2_waybel_0(C_4,k3_yellow_1(B_3))
      | v1_xboole_0(C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_2)))
      | v1_xboole_0(B_3)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_241,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_239,c_10])).

tff(c_244,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_241])).

tff(c_245,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_174,c_42,c_244])).

tff(c_248,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_245])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_248])).

tff(c_253,plain,(
    r2_hidden('#skF_3',k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_30,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(A_19,B_20)
      | ~ r2_hidden(A_19,k4_xboole_0(B_20,k1_tarski(C_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_258,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_253,c_30])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_258])).

tff(c_264,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(A_19,k4_xboole_0(B_20,k1_tarski(C_21)))
      | C_21 = A_19
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_354,plain,(
    ! [A_95,B_96,C_97] :
      ( l1_waybel_0(k3_yellow19(A_95,B_96,C_97),A_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_96))))
      | ~ v13_waybel_0(C_97,k3_yellow_1(B_96))
      | ~ v2_waybel_0(C_97,k3_yellow_1(B_96))
      | v1_xboole_0(C_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_359,plain,(
    ! [A_95] :
      ( l1_waybel_0(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'),A_95)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_36,c_354])).

tff(c_363,plain,(
    ! [A_95] :
      ( l1_waybel_0(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'),A_95)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_359])).

tff(c_364,plain,(
    ! [A_95] :
      ( l1_waybel_0(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'),A_95)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_363])).

tff(c_365,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_379,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_365,c_14])).

tff(c_382,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_379])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_382])).

tff(c_386,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_387,plain,(
    ! [A_101] :
      ( l1_waybel_0(k3_yellow19(A_101,k2_struct_0('#skF_1'),'#skF_2'),A_101)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_390,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_387])).

tff(c_393,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_390])).

tff(c_394,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_393])).

tff(c_267,plain,(
    ! [A_70,B_71,C_72] :
      ( k7_subset_1(A_70,B_71,C_72) = k4_xboole_0(B_71,C_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_275,plain,(
    ! [C_72] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_72) = k4_xboole_0('#skF_2',C_72) ),
    inference(resolution,[status(thm)],[c_36,c_267])).

tff(c_414,plain,(
    ! [A_106,B_107] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_106))),B_107,k1_tarski(k1_xboole_0)) = k2_yellow19(A_106,k3_yellow19(A_106,k2_struct_0(A_106),B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_106)))))
      | ~ v13_waybel_0(B_107,k3_yellow_1(k2_struct_0(A_106)))
      | ~ v2_waybel_0(B_107,k3_yellow_1(k2_struct_0(A_106)))
      | v1_xboole_0(B_107)
      | ~ l1_struct_0(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_419,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_414])).

tff(c_423,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_275,c_419])).

tff(c_424,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_423])).

tff(c_20,plain,(
    ! [C_15,A_9,B_13] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ r2_hidden(C_15,k2_yellow19(A_9,B_13))
      | ~ l1_waybel_0(B_13,A_9)
      | v2_struct_0(B_13)
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_433,plain,(
    ! [C_15] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_20])).

tff(c_445,plain,(
    ! [C_15] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_394,c_433])).

tff(c_446,plain,(
    ! [C_15] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_445])).

tff(c_452,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_454,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_452,c_10])).

tff(c_457,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_454])).

tff(c_458,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_386,c_42,c_457])).

tff(c_461,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_458])).

tff(c_465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_461])).

tff(c_467,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_22,plain,(
    ! [A_9,B_13,C_15] :
      ( r1_waybel_0(A_9,B_13,C_15)
      | ~ r2_hidden(C_15,k2_yellow19(A_9,B_13))
      | ~ l1_waybel_0(B_13,A_9)
      | v2_struct_0(B_13)
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_436,plain,(
    ! [C_15] :
      ( r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_15)
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_22])).

tff(c_448,plain,(
    ! [C_15] :
      ( r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_15)
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_394,c_436])).

tff(c_449,plain,(
    ! [C_15] :
      ( r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_15)
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_448])).

tff(c_468,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_467,c_468])).

tff(c_539,plain,(
    ! [C_116] :
      ( r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_116)
      | ~ r2_hidden(C_116,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))) ) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_263,plain,(
    ~ r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_543,plain,(
    ~ r2_hidden('#skF_3',k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_539,c_263])).

tff(c_566,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_543])).

tff(c_569,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_566])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_12,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_578,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_55])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_578])).

%------------------------------------------------------------------------------
