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
% DateTime   : Thu Dec  3 10:19:48 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 175 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  283 ( 723 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( r1_tarski(C,D)
                     => r1_tarski(k3_orders_2(A,C,B),k3_orders_2(A,D,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_40] : r1_tarski(A_40,A_40) ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_1,B_2,B_44] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_44)
      | ~ r1_tarski(A_1,B_44)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_56,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k3_orders_2(A_49,B_50,C_51),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_156,plain,(
    ! [A_84,A_85,B_86,C_87] :
      ( m1_subset_1(A_84,u1_struct_0(A_85))
      | ~ r2_hidden(A_84,k3_orders_2(A_85,B_86,C_87))
      | ~ m1_subset_1(C_87,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_56,c_8])).

tff(c_169,plain,(
    ! [C_92,B_88,B_89,A_91,A_90] :
      ( m1_subset_1('#skF_1'(A_90,B_89),u1_struct_0(A_91))
      | ~ m1_subset_1(C_92,u1_struct_0(A_91))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_orders_2(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v4_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91)
      | ~ r1_tarski(A_90,k3_orders_2(A_91,B_88,C_92))
      | r1_tarski(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_48,c_156])).

tff(c_173,plain,(
    ! [A_90,B_89,C_92] :
      ( m1_subset_1('#skF_1'(A_90,B_89),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_92,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_90,k3_orders_2('#skF_2','#skF_4',C_92))
      | r1_tarski(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_24,c_169])).

tff(c_179,plain,(
    ! [A_90,B_89,C_92] :
      ( m1_subset_1('#skF_1'(A_90,B_89),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_92,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_90,k3_orders_2('#skF_2','#skF_4',C_92))
      | r1_tarski(A_90,B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_173])).

tff(c_185,plain,(
    ! [A_93,B_94,C_95] :
      ( m1_subset_1('#skF_1'(A_93,B_94),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_93,k3_orders_2('#skF_2','#skF_4',C_95))
      | r1_tarski(A_93,B_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_179])).

tff(c_189,plain,(
    ! [C_95,B_94] :
      ( m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_95),B_94),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_95),B_94) ) ),
    inference(resolution,[status(thm)],[c_43,c_185])).

tff(c_71,plain,(
    ! [B_57,D_58,A_59,C_60] :
      ( r2_hidden(B_57,D_58)
      | ~ r2_hidden(B_57,k3_orders_2(A_59,D_58,C_60))
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(C_60,u1_struct_0(A_59))
      | ~ m1_subset_1(B_57,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_289,plain,(
    ! [A_127,D_128,C_129,B_130] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_127,D_128,C_129),B_130),D_128)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_127,D_128,C_129),B_130),u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127)
      | r1_tarski(k3_orders_2(A_127,D_128,C_129),B_130) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_295,plain,(
    ! [C_95,B_94] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_95),B_94),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_95),B_94) ) ),
    inference(resolution,[status(thm)],[c_189,c_289])).

tff(c_309,plain,(
    ! [C_95,B_94] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_95),B_94),'#skF_4')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_95),B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_24,c_295])).

tff(c_341,plain,(
    ! [C_134,B_135] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_134),B_135),'#skF_4')
      | ~ m1_subset_1(C_134,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_134),B_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_309])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_473,plain,(
    ! [C_162,B_163,B_164] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_162),B_163),B_164)
      | ~ r1_tarski('#skF_4',B_164)
      | ~ m1_subset_1(C_162,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_162),B_163) ) ),
    inference(resolution,[status(thm)],[c_341,c_2])).

tff(c_499,plain,(
    ! [B_164,C_162] :
      ( ~ r1_tarski('#skF_4',B_164)
      | ~ m1_subset_1(C_162,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_162),B_164) ) ),
    inference(resolution,[status(thm)],[c_473,c_4])).

tff(c_20,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_62,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_56)
      | ~ r1_tarski(A_54,B_56)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_80,plain,(
    ! [A_61,B_62,B_63,B_64] :
      ( r2_hidden('#skF_1'(A_61,B_62),B_63)
      | ~ r1_tarski(B_64,B_63)
      | ~ r1_tarski(A_61,B_64)
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_87,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),'#skF_5')
      | ~ r1_tarski(A_65,'#skF_4')
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_94,plain,(
    ! [A_65,B_66,B_2] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_2)
      | ~ r1_tarski('#skF_5',B_2)
      | ~ r1_tarski(A_65,'#skF_4')
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_49,plain,(
    ! [A_46,C_47,B_48] :
      ( m1_subset_1(A_46,C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_46,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_122,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( r2_orders_2(A_73,B_74,C_75)
      | ~ r2_hidden(B_74,k3_orders_2(A_73,D_76,C_75))
      | ~ m1_subset_1(D_76,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1122,plain,(
    ! [C_244,D_245,A_248,A_247,B_246] :
      ( r2_orders_2(A_248,'#skF_1'(A_247,B_246),C_244)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_subset_1(C_244,u1_struct_0(A_248))
      | ~ m1_subset_1('#skF_1'(A_247,B_246),u1_struct_0(A_248))
      | ~ l1_orders_2(A_248)
      | ~ v5_orders_2(A_248)
      | ~ v4_orders_2(A_248)
      | ~ v3_orders_2(A_248)
      | v2_struct_0(A_248)
      | ~ r1_tarski(A_247,k3_orders_2(A_248,D_245,C_244))
      | r1_tarski(A_247,B_246) ) ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_1126,plain,(
    ! [A_247,B_246,C_244] :
      ( r2_orders_2('#skF_2','#skF_1'(A_247,B_246),C_244)
      | ~ m1_subset_1(C_244,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_247,B_246),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_247,k3_orders_2('#skF_2','#skF_4',C_244))
      | r1_tarski(A_247,B_246) ) ),
    inference(resolution,[status(thm)],[c_24,c_1122])).

tff(c_1132,plain,(
    ! [A_247,B_246,C_244] :
      ( r2_orders_2('#skF_2','#skF_1'(A_247,B_246),C_244)
      | ~ m1_subset_1(C_244,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_247,B_246),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_247,k3_orders_2('#skF_2','#skF_4',C_244))
      | r1_tarski(A_247,B_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_1126])).

tff(c_1138,plain,(
    ! [A_249,B_250,C_251] :
      ( r2_orders_2('#skF_2','#skF_1'(A_249,B_250),C_251)
      | ~ m1_subset_1(C_251,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_249,B_250),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_249,k3_orders_2('#skF_2','#skF_4',C_251))
      | r1_tarski(A_249,B_250) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1132])).

tff(c_1160,plain,(
    ! [A_252,B_253,C_254] :
      ( r2_orders_2('#skF_2','#skF_1'(A_252,B_253),C_254)
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_252,k3_orders_2('#skF_2','#skF_4',C_254))
      | r1_tarski(A_252,B_253)
      | ~ r2_hidden('#skF_1'(A_252,B_253),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_55,c_1138])).

tff(c_196,plain,(
    ! [B_101,A_102,D_103,C_104] :
      ( r2_hidden(B_101,k3_orders_2(A_102,D_103,C_104))
      | ~ r2_hidden(B_101,D_103)
      | ~ r2_orders_2(A_102,B_101,C_104)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_101,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102)
      | ~ v4_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_202,plain,(
    ! [B_101,C_104] :
      ( r2_hidden(B_101,k3_orders_2('#skF_2','#skF_5',C_104))
      | ~ r2_hidden(B_101,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_101,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_196])).

tff(c_210,plain,(
    ! [B_101,C_104] :
      ( r2_hidden(B_101,k3_orders_2('#skF_2','#skF_5',C_104))
      | ~ r2_hidden(B_101,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_101,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_202])).

tff(c_240,plain,(
    ! [B_109,C_110] :
      ( r2_hidden(B_109,k3_orders_2('#skF_2','#skF_5',C_110))
      | ~ r2_hidden(B_109,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_109,C_110)
      | ~ m1_subset_1(C_110,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_210])).

tff(c_266,plain,(
    ! [A_1,C_110] :
      ( r1_tarski(A_1,k3_orders_2('#skF_2','#skF_5',C_110))
      | ~ r2_hidden('#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5',C_110)),'#skF_5')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5',C_110)),C_110)
      | ~ m1_subset_1(C_110,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5',C_110)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_240,c_4])).

tff(c_1484,plain,(
    ! [A_302,C_303] :
      ( ~ m1_subset_1('#skF_1'(A_302,k3_orders_2('#skF_2','#skF_5',C_303)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_303,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_302,k3_orders_2('#skF_2','#skF_4',C_303))
      | r1_tarski(A_302,k3_orders_2('#skF_2','#skF_5',C_303))
      | ~ r2_hidden('#skF_1'(A_302,k3_orders_2('#skF_2','#skF_5',C_303)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1160,c_266])).

tff(c_1511,plain,(
    ! [C_304,A_305] :
      ( ~ m1_subset_1(C_304,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_305,k3_orders_2('#skF_2','#skF_4',C_304))
      | r1_tarski(A_305,k3_orders_2('#skF_2','#skF_5',C_304))
      | ~ r2_hidden('#skF_1'(A_305,k3_orders_2('#skF_2','#skF_5',C_304)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_55,c_1484])).

tff(c_1555,plain,(
    ! [C_304,A_65] :
      ( ~ m1_subset_1(C_304,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_65,k3_orders_2('#skF_2','#skF_4',C_304))
      | ~ r1_tarski('#skF_5','#skF_5')
      | ~ r1_tarski(A_65,'#skF_4')
      | r1_tarski(A_65,k3_orders_2('#skF_2','#skF_5',C_304)) ) ),
    inference(resolution,[status(thm)],[c_94,c_1511])).

tff(c_1594,plain,(
    ! [C_306,A_307] :
      ( ~ m1_subset_1(C_306,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_307,k3_orders_2('#skF_2','#skF_4',C_306))
      | ~ r1_tarski(A_307,'#skF_4')
      | r1_tarski(A_307,k3_orders_2('#skF_2','#skF_5',C_306)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_1555])).

tff(c_18,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1633,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_4','#skF_3'))
    | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1594,c_18])).

tff(c_1655,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_26,c_1633])).

tff(c_1724,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_499,c_1655])).

tff(c_1734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_43,c_1724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.90  
% 4.44/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.90  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.44/1.90  
% 4.44/1.90  %Foreground sorts:
% 4.44/1.90  
% 4.44/1.90  
% 4.44/1.90  %Background operators:
% 4.44/1.90  
% 4.44/1.90  
% 4.44/1.90  %Foreground operators:
% 4.44/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.44/1.90  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.44/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.44/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.44/1.90  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 4.44/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.44/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.44/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.44/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.44/1.90  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.44/1.90  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.44/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.44/1.90  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.44/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.44/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.44/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.44/1.90  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.44/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.44/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.44/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.44/1.91  
% 4.80/1.93  tff(f_106, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, D) => r1_tarski(k3_orders_2(A, C, B), k3_orders_2(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_orders_2)).
% 4.80/1.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.80/1.93  tff(f_55, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 4.80/1.93  tff(f_38, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.80/1.93  tff(f_81, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 4.80/1.93  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_38, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), A_40) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.80/1.93  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.80/1.93  tff(c_43, plain, (![A_40]: (r1_tarski(A_40, A_40))), inference(resolution, [status(thm)], [c_38, c_4])).
% 4.80/1.93  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_34, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_32, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_28, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.80/1.93  tff(c_45, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.80/1.93  tff(c_48, plain, (![A_1, B_2, B_44]: (r2_hidden('#skF_1'(A_1, B_2), B_44) | ~r1_tarski(A_1, B_44) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_45])).
% 4.80/1.93  tff(c_56, plain, (![A_49, B_50, C_51]: (m1_subset_1(k3_orders_2(A_49, B_50, C_51), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.80/1.93  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.80/1.93  tff(c_156, plain, (![A_84, A_85, B_86, C_87]: (m1_subset_1(A_84, u1_struct_0(A_85)) | ~r2_hidden(A_84, k3_orders_2(A_85, B_86, C_87)) | ~m1_subset_1(C_87, u1_struct_0(A_85)) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(resolution, [status(thm)], [c_56, c_8])).
% 4.80/1.93  tff(c_169, plain, (![C_92, B_88, B_89, A_91, A_90]: (m1_subset_1('#skF_1'(A_90, B_89), u1_struct_0(A_91)) | ~m1_subset_1(C_92, u1_struct_0(A_91)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_orders_2(A_91) | ~v5_orders_2(A_91) | ~v4_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91) | ~r1_tarski(A_90, k3_orders_2(A_91, B_88, C_92)) | r1_tarski(A_90, B_89))), inference(resolution, [status(thm)], [c_48, c_156])).
% 4.80/1.93  tff(c_173, plain, (![A_90, B_89, C_92]: (m1_subset_1('#skF_1'(A_90, B_89), u1_struct_0('#skF_2')) | ~m1_subset_1(C_92, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_90, k3_orders_2('#skF_2', '#skF_4', C_92)) | r1_tarski(A_90, B_89))), inference(resolution, [status(thm)], [c_24, c_169])).
% 4.80/1.93  tff(c_179, plain, (![A_90, B_89, C_92]: (m1_subset_1('#skF_1'(A_90, B_89), u1_struct_0('#skF_2')) | ~m1_subset_1(C_92, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_90, k3_orders_2('#skF_2', '#skF_4', C_92)) | r1_tarski(A_90, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_173])).
% 4.80/1.93  tff(c_185, plain, (![A_93, B_94, C_95]: (m1_subset_1('#skF_1'(A_93, B_94), u1_struct_0('#skF_2')) | ~m1_subset_1(C_95, u1_struct_0('#skF_2')) | ~r1_tarski(A_93, k3_orders_2('#skF_2', '#skF_4', C_95)) | r1_tarski(A_93, B_94))), inference(negUnitSimplification, [status(thm)], [c_36, c_179])).
% 4.80/1.93  tff(c_189, plain, (![C_95, B_94]: (m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_95), B_94), u1_struct_0('#skF_2')) | ~m1_subset_1(C_95, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_95), B_94))), inference(resolution, [status(thm)], [c_43, c_185])).
% 4.80/1.93  tff(c_71, plain, (![B_57, D_58, A_59, C_60]: (r2_hidden(B_57, D_58) | ~r2_hidden(B_57, k3_orders_2(A_59, D_58, C_60)) | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(C_60, u1_struct_0(A_59)) | ~m1_subset_1(B_57, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.80/1.93  tff(c_289, plain, (![A_127, D_128, C_129, B_130]: (r2_hidden('#skF_1'(k3_orders_2(A_127, D_128, C_129), B_130), D_128) | ~m1_subset_1(D_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_127, D_128, C_129), B_130), u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127) | r1_tarski(k3_orders_2(A_127, D_128, C_129), B_130))), inference(resolution, [status(thm)], [c_6, c_71])).
% 4.80/1.93  tff(c_295, plain, (![C_95, B_94]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_95), B_94), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_95, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_95), B_94))), inference(resolution, [status(thm)], [c_189, c_289])).
% 4.80/1.93  tff(c_309, plain, (![C_95, B_94]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_95), B_94), '#skF_4') | v2_struct_0('#skF_2') | ~m1_subset_1(C_95, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_95), B_94))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_24, c_295])).
% 4.80/1.93  tff(c_341, plain, (![C_134, B_135]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_134), B_135), '#skF_4') | ~m1_subset_1(C_134, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_134), B_135))), inference(negUnitSimplification, [status(thm)], [c_36, c_309])).
% 4.80/1.93  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.80/1.93  tff(c_473, plain, (![C_162, B_163, B_164]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_162), B_163), B_164) | ~r1_tarski('#skF_4', B_164) | ~m1_subset_1(C_162, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_162), B_163))), inference(resolution, [status(thm)], [c_341, c_2])).
% 4.80/1.93  tff(c_499, plain, (![B_164, C_162]: (~r1_tarski('#skF_4', B_164) | ~m1_subset_1(C_162, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_162), B_164))), inference(resolution, [status(thm)], [c_473, c_4])).
% 4.80/1.93  tff(c_20, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_62, plain, (![A_54, B_55, B_56]: (r2_hidden('#skF_1'(A_54, B_55), B_56) | ~r1_tarski(A_54, B_56) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_6, c_45])).
% 4.80/1.93  tff(c_80, plain, (![A_61, B_62, B_63, B_64]: (r2_hidden('#skF_1'(A_61, B_62), B_63) | ~r1_tarski(B_64, B_63) | ~r1_tarski(A_61, B_64) | r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_62, c_2])).
% 4.80/1.93  tff(c_87, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), '#skF_5') | ~r1_tarski(A_65, '#skF_4') | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_20, c_80])).
% 4.80/1.93  tff(c_94, plain, (![A_65, B_66, B_2]: (r2_hidden('#skF_1'(A_65, B_66), B_2) | ~r1_tarski('#skF_5', B_2) | ~r1_tarski(A_65, '#skF_4') | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_87, c_2])).
% 4.80/1.93  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_49, plain, (![A_46, C_47, B_48]: (m1_subset_1(A_46, C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.80/1.93  tff(c_55, plain, (![A_46]: (m1_subset_1(A_46, u1_struct_0('#skF_2')) | ~r2_hidden(A_46, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_49])).
% 4.80/1.93  tff(c_122, plain, (![A_73, B_74, C_75, D_76]: (r2_orders_2(A_73, B_74, C_75) | ~r2_hidden(B_74, k3_orders_2(A_73, D_76, C_75)) | ~m1_subset_1(D_76, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.80/1.93  tff(c_1122, plain, (![C_244, D_245, A_248, A_247, B_246]: (r2_orders_2(A_248, '#skF_1'(A_247, B_246), C_244) | ~m1_subset_1(D_245, k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_subset_1(C_244, u1_struct_0(A_248)) | ~m1_subset_1('#skF_1'(A_247, B_246), u1_struct_0(A_248)) | ~l1_orders_2(A_248) | ~v5_orders_2(A_248) | ~v4_orders_2(A_248) | ~v3_orders_2(A_248) | v2_struct_0(A_248) | ~r1_tarski(A_247, k3_orders_2(A_248, D_245, C_244)) | r1_tarski(A_247, B_246))), inference(resolution, [status(thm)], [c_48, c_122])).
% 4.80/1.93  tff(c_1126, plain, (![A_247, B_246, C_244]: (r2_orders_2('#skF_2', '#skF_1'(A_247, B_246), C_244) | ~m1_subset_1(C_244, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_247, B_246), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_247, k3_orders_2('#skF_2', '#skF_4', C_244)) | r1_tarski(A_247, B_246))), inference(resolution, [status(thm)], [c_24, c_1122])).
% 4.80/1.93  tff(c_1132, plain, (![A_247, B_246, C_244]: (r2_orders_2('#skF_2', '#skF_1'(A_247, B_246), C_244) | ~m1_subset_1(C_244, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_247, B_246), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_247, k3_orders_2('#skF_2', '#skF_4', C_244)) | r1_tarski(A_247, B_246))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_1126])).
% 4.80/1.93  tff(c_1138, plain, (![A_249, B_250, C_251]: (r2_orders_2('#skF_2', '#skF_1'(A_249, B_250), C_251) | ~m1_subset_1(C_251, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_249, B_250), u1_struct_0('#skF_2')) | ~r1_tarski(A_249, k3_orders_2('#skF_2', '#skF_4', C_251)) | r1_tarski(A_249, B_250))), inference(negUnitSimplification, [status(thm)], [c_36, c_1132])).
% 4.80/1.93  tff(c_1160, plain, (![A_252, B_253, C_254]: (r2_orders_2('#skF_2', '#skF_1'(A_252, B_253), C_254) | ~m1_subset_1(C_254, u1_struct_0('#skF_2')) | ~r1_tarski(A_252, k3_orders_2('#skF_2', '#skF_4', C_254)) | r1_tarski(A_252, B_253) | ~r2_hidden('#skF_1'(A_252, B_253), '#skF_5'))), inference(resolution, [status(thm)], [c_55, c_1138])).
% 4.80/1.93  tff(c_196, plain, (![B_101, A_102, D_103, C_104]: (r2_hidden(B_101, k3_orders_2(A_102, D_103, C_104)) | ~r2_hidden(B_101, D_103) | ~r2_orders_2(A_102, B_101, C_104) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_101, u1_struct_0(A_102)) | ~l1_orders_2(A_102) | ~v5_orders_2(A_102) | ~v4_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.80/1.93  tff(c_202, plain, (![B_101, C_104]: (r2_hidden(B_101, k3_orders_2('#skF_2', '#skF_5', C_104)) | ~r2_hidden(B_101, '#skF_5') | ~r2_orders_2('#skF_2', B_101, C_104) | ~m1_subset_1(C_104, u1_struct_0('#skF_2')) | ~m1_subset_1(B_101, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_196])).
% 4.80/1.93  tff(c_210, plain, (![B_101, C_104]: (r2_hidden(B_101, k3_orders_2('#skF_2', '#skF_5', C_104)) | ~r2_hidden(B_101, '#skF_5') | ~r2_orders_2('#skF_2', B_101, C_104) | ~m1_subset_1(C_104, u1_struct_0('#skF_2')) | ~m1_subset_1(B_101, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_202])).
% 4.80/1.93  tff(c_240, plain, (![B_109, C_110]: (r2_hidden(B_109, k3_orders_2('#skF_2', '#skF_5', C_110)) | ~r2_hidden(B_109, '#skF_5') | ~r2_orders_2('#skF_2', B_109, C_110) | ~m1_subset_1(C_110, u1_struct_0('#skF_2')) | ~m1_subset_1(B_109, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_210])).
% 4.80/1.93  tff(c_266, plain, (![A_1, C_110]: (r1_tarski(A_1, k3_orders_2('#skF_2', '#skF_5', C_110)) | ~r2_hidden('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', C_110)), '#skF_5') | ~r2_orders_2('#skF_2', '#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', C_110)), C_110) | ~m1_subset_1(C_110, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', C_110)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_240, c_4])).
% 4.80/1.93  tff(c_1484, plain, (![A_302, C_303]: (~m1_subset_1('#skF_1'(A_302, k3_orders_2('#skF_2', '#skF_5', C_303)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_303, u1_struct_0('#skF_2')) | ~r1_tarski(A_302, k3_orders_2('#skF_2', '#skF_4', C_303)) | r1_tarski(A_302, k3_orders_2('#skF_2', '#skF_5', C_303)) | ~r2_hidden('#skF_1'(A_302, k3_orders_2('#skF_2', '#skF_5', C_303)), '#skF_5'))), inference(resolution, [status(thm)], [c_1160, c_266])).
% 4.80/1.93  tff(c_1511, plain, (![C_304, A_305]: (~m1_subset_1(C_304, u1_struct_0('#skF_2')) | ~r1_tarski(A_305, k3_orders_2('#skF_2', '#skF_4', C_304)) | r1_tarski(A_305, k3_orders_2('#skF_2', '#skF_5', C_304)) | ~r2_hidden('#skF_1'(A_305, k3_orders_2('#skF_2', '#skF_5', C_304)), '#skF_5'))), inference(resolution, [status(thm)], [c_55, c_1484])).
% 4.80/1.93  tff(c_1555, plain, (![C_304, A_65]: (~m1_subset_1(C_304, u1_struct_0('#skF_2')) | ~r1_tarski(A_65, k3_orders_2('#skF_2', '#skF_4', C_304)) | ~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski(A_65, '#skF_4') | r1_tarski(A_65, k3_orders_2('#skF_2', '#skF_5', C_304)))), inference(resolution, [status(thm)], [c_94, c_1511])).
% 4.80/1.93  tff(c_1594, plain, (![C_306, A_307]: (~m1_subset_1(C_306, u1_struct_0('#skF_2')) | ~r1_tarski(A_307, k3_orders_2('#skF_2', '#skF_4', C_306)) | ~r1_tarski(A_307, '#skF_4') | r1_tarski(A_307, k3_orders_2('#skF_2', '#skF_5', C_306)))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_1555])).
% 4.80/1.93  tff(c_18, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.93  tff(c_1633, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1594, c_18])).
% 4.80/1.93  tff(c_1655, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_26, c_1633])).
% 4.80/1.93  tff(c_1724, plain, (~r1_tarski('#skF_4', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_499, c_1655])).
% 4.80/1.93  tff(c_1734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_43, c_1724])).
% 4.80/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.93  
% 4.80/1.93  Inference rules
% 4.80/1.93  ----------------------
% 4.80/1.93  #Ref     : 0
% 4.80/1.93  #Sup     : 384
% 4.80/1.93  #Fact    : 0
% 4.80/1.93  #Define  : 0
% 4.80/1.93  #Split   : 2
% 4.80/1.93  #Chain   : 0
% 4.80/1.93  #Close   : 0
% 4.80/1.93  
% 4.80/1.93  Ordering : KBO
% 4.80/1.93  
% 4.80/1.93  Simplification rules
% 4.80/1.93  ----------------------
% 4.80/1.93  #Subsume      : 161
% 4.80/1.93  #Demod        : 216
% 4.80/1.93  #Tautology    : 23
% 4.80/1.93  #SimpNegUnit  : 37
% 4.80/1.93  #BackRed      : 0
% 4.80/1.93  
% 4.80/1.93  #Partial instantiations: 0
% 4.80/1.93  #Strategies tried      : 1
% 4.80/1.93  
% 4.80/1.93  Timing (in seconds)
% 4.80/1.93  ----------------------
% 4.80/1.93  Preprocessing        : 0.35
% 4.80/1.93  Parsing              : 0.19
% 4.80/1.93  CNF conversion       : 0.03
% 4.80/1.93  Main loop            : 0.74
% 4.80/1.93  Inferencing          : 0.27
% 4.80/1.93  Reduction            : 0.19
% 4.80/1.93  Demodulation         : 0.13
% 4.80/1.93  BG Simplification    : 0.02
% 4.80/1.93  Subsumption          : 0.22
% 4.80/1.93  Abstraction          : 0.03
% 4.80/1.93  MUC search           : 0.00
% 4.80/1.93  Cooper               : 0.00
% 4.80/1.93  Total                : 1.14
% 4.80/1.93  Index Insertion      : 0.00
% 4.80/1.93  Index Deletion       : 0.00
% 4.80/1.93  Index Matching       : 0.00
% 4.80/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
