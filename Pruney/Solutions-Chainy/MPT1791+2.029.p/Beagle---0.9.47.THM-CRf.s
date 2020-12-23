%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:53 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 133 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 394 expanded)
%              Number of equality atoms :   23 (  71 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A,B))))
             => ( C = B
               => v3_pre_topc(C,k6_tmap_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_41,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_63,plain,(
    ! [A_28,B_29] :
      ( u1_struct_0(k6_tmap_1(A_28,B_29)) = u1_struct_0(A_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_69,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_66])).

tff(c_70,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_69])).

tff(c_201,plain,(
    ! [C_43,A_44] :
      ( v3_pre_topc(C_43,k6_tmap_1(A_44,C_43))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_44,C_43))))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_204,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_201])).

tff(c_206,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_26,c_204])).

tff(c_207,plain,(
    v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_206])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_40])).

tff(c_208,plain,(
    ! [B_45,A_46] :
      ( v3_pre_topc(B_45,A_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_46),u1_pre_topc(A_46)))))
      | ~ v3_pre_topc(B_45,g1_pre_topc(u1_struct_0(A_46),u1_pre_topc(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_220,plain,(
    ! [B_45] :
      ( v3_pre_topc(B_45,'#skF_1')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2'))))
      | ~ v3_pre_topc(B_45,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_208])).

tff(c_226,plain,(
    ! [B_47] :
      ( v3_pre_topc(B_47,'#skF_1')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v3_pre_topc(B_47,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_42,c_70,c_220])).

tff(c_229,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_226])).

tff(c_232,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_229])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_232])).

tff(c_235,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_237,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_237])).

tff(c_240,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_236,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_249,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,u1_pre_topc(A_51))
      | ~ v3_pre_topc(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_252,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_249])).

tff(c_255,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_236,c_252])).

tff(c_314,plain,(
    ! [A_60,B_61] :
      ( k5_tmap_1(A_60,B_61) = u1_pre_topc(A_60)
      | ~ r2_hidden(B_61,u1_pre_topc(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_320,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_314])).

tff(c_324,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_255,c_320])).

tff(c_325,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_324])).

tff(c_341,plain,(
    ! [A_62,B_63] :
      ( g1_pre_topc(u1_struct_0(A_62),k5_tmap_1(A_62,B_63)) = k6_tmap_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_345,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_341])).

tff(c_349,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_325,c_345])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_240,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:39:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.45/1.35  
% 2.45/1.35  %Foreground sorts:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Background operators:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Foreground operators:
% 2.45/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.45/1.35  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.45/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.35  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.45/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.45/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.35  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.45/1.35  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.45/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.35  
% 2.64/1.37  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 2.64/1.37  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.64/1.37  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tmap_1)).
% 2.64/1.37  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 2.64/1.37  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.64/1.37  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 2.64/1.37  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.64/1.37  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.37  tff(c_34, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.37  tff(c_41, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.64/1.37  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.37  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.37  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.37  tff(c_63, plain, (![A_28, B_29]: (u1_struct_0(k6_tmap_1(A_28, B_29))=u1_struct_0(A_28) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.64/1.37  tff(c_66, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_63])).
% 2.64/1.37  tff(c_69, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_66])).
% 2.64/1.37  tff(c_70, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_69])).
% 2.64/1.37  tff(c_201, plain, (![C_43, A_44]: (v3_pre_topc(C_43, k6_tmap_1(A_44, C_43)) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_44, C_43)))) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.64/1.37  tff(c_204, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70, c_201])).
% 2.64/1.37  tff(c_206, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_26, c_204])).
% 2.64/1.37  tff(c_207, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_206])).
% 2.64/1.37  tff(c_40, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.37  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_41, c_40])).
% 2.64/1.37  tff(c_208, plain, (![B_45, A_46]: (v3_pre_topc(B_45, A_46) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_46), u1_pre_topc(A_46))))) | ~v3_pre_topc(B_45, g1_pre_topc(u1_struct_0(A_46), u1_pre_topc(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.37  tff(c_220, plain, (![B_45]: (v3_pre_topc(B_45, '#skF_1') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')))) | ~v3_pre_topc(B_45, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_208])).
% 2.64/1.37  tff(c_226, plain, (![B_47]: (v3_pre_topc(B_47, '#skF_1') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc(B_47, k6_tmap_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_42, c_70, c_220])).
% 2.64/1.37  tff(c_229, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_226])).
% 2.64/1.37  tff(c_232, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_229])).
% 2.64/1.37  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_232])).
% 2.64/1.37  tff(c_235, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.64/1.37  tff(c_237, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.64/1.37  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_237])).
% 2.64/1.37  tff(c_240, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.64/1.37  tff(c_236, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.64/1.37  tff(c_249, plain, (![B_50, A_51]: (r2_hidden(B_50, u1_pre_topc(A_51)) | ~v3_pre_topc(B_50, A_51) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.64/1.37  tff(c_252, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_249])).
% 2.64/1.37  tff(c_255, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_236, c_252])).
% 2.64/1.37  tff(c_314, plain, (![A_60, B_61]: (k5_tmap_1(A_60, B_61)=u1_pre_topc(A_60) | ~r2_hidden(B_61, u1_pre_topc(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.37  tff(c_320, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_314])).
% 2.64/1.37  tff(c_324, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_255, c_320])).
% 2.64/1.37  tff(c_325, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_324])).
% 2.64/1.37  tff(c_341, plain, (![A_62, B_63]: (g1_pre_topc(u1_struct_0(A_62), k5_tmap_1(A_62, B_63))=k6_tmap_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.64/1.37  tff(c_345, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_341])).
% 2.64/1.37  tff(c_349, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_325, c_345])).
% 2.64/1.37  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_240, c_349])).
% 2.64/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  Inference rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Ref     : 0
% 2.64/1.37  #Sup     : 67
% 2.64/1.37  #Fact    : 0
% 2.64/1.37  #Define  : 0
% 2.64/1.37  #Split   : 4
% 2.64/1.37  #Chain   : 0
% 2.64/1.37  #Close   : 0
% 2.64/1.37  
% 2.64/1.37  Ordering : KBO
% 2.64/1.37  
% 2.64/1.37  Simplification rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Subsume      : 11
% 2.64/1.37  #Demod        : 90
% 2.64/1.37  #Tautology    : 23
% 2.64/1.37  #SimpNegUnit  : 16
% 2.64/1.37  #BackRed      : 1
% 2.64/1.37  
% 2.64/1.37  #Partial instantiations: 0
% 2.64/1.37  #Strategies tried      : 1
% 2.64/1.37  
% 2.64/1.37  Timing (in seconds)
% 2.64/1.37  ----------------------
% 2.64/1.37  Preprocessing        : 0.34
% 2.64/1.37  Parsing              : 0.18
% 2.64/1.37  CNF conversion       : 0.02
% 2.64/1.37  Main loop            : 0.24
% 2.64/1.37  Inferencing          : 0.08
% 2.64/1.37  Reduction            : 0.08
% 2.64/1.37  Demodulation         : 0.06
% 2.64/1.37  BG Simplification    : 0.02
% 2.64/1.37  Subsumption          : 0.04
% 2.64/1.38  Abstraction          : 0.02
% 2.64/1.38  MUC search           : 0.00
% 2.64/1.38  Cooper               : 0.00
% 2.64/1.38  Total                : 0.61
% 2.64/1.38  Index Insertion      : 0.00
% 2.64/1.38  Index Deletion       : 0.00
% 2.64/1.38  Index Matching       : 0.00
% 2.64/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
