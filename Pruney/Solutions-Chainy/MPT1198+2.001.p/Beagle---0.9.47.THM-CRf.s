%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:12 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 101 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 381 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v5_lattices > v2_struct_0 > l2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v5_lattices(A)
          & l2_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r1_lattices(A,B,C)
                        & r1_lattices(A,C,D) )
                     => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_lattices)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v5_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k1_lattices(A,B,k1_lattices(A,C,D)) = k1_lattices(A,k1_lattices(A,B,C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).

tff(c_16,plain,(
    ~ r1_lattices('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    l2_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_57,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_lattices(A_51,B_52,C_53)
      | k1_lattices(A_51,B_52,C_53) != C_53
      | ~ m1_subset_1(C_53,u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,u1_struct_0(A_51))
      | ~ l2_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,(
    ! [B_52] :
      ( r1_lattices('#skF_4',B_52,'#skF_7')
      | k1_lattices('#skF_4',B_52,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4'))
      | ~ l2_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_79,plain,(
    ! [B_52] :
      ( r1_lattices('#skF_4',B_52,'#skF_7')
      | k1_lattices('#skF_4',B_52,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_67])).

tff(c_126,plain,(
    ! [B_55] :
      ( r1_lattices('#skF_4',B_55,'#skF_7')
      | k1_lattices('#skF_4',B_55,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_79])).

tff(c_147,plain,
    ( r1_lattices('#skF_4','#skF_5','#skF_7')
    | k1_lattices('#skF_4','#skF_5','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_166,plain,(
    k1_lattices('#skF_4','#skF_5','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_147])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    r1_lattices('#skF_4','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_lattices(A_48,B_49,C_50) = C_50
      | ~ r1_lattices(A_48,B_49,C_50)
      | ~ m1_subset_1(C_50,u1_struct_0(A_48))
      | ~ m1_subset_1(B_49,u1_struct_0(A_48))
      | ~ l2_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,
    ( k1_lattices('#skF_4','#skF_6','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_36])).

tff(c_47,plain,
    ( k1_lattices('#skF_4','#skF_6','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_40])).

tff(c_48,plain,(
    k1_lattices('#skF_4','#skF_6','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_47])).

tff(c_20,plain,(
    r1_lattices('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,
    ( k1_lattices('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_43,plain,
    ( k1_lattices('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_38])).

tff(c_44,plain,(
    k1_lattices('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_43])).

tff(c_30,plain,(
    v5_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_217,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k1_lattices(A_62,k1_lattices(A_62,B_63,C_64),D_65) = k1_lattices(A_62,B_63,k1_lattices(A_62,C_64,D_65))
      | ~ m1_subset_1(D_65,u1_struct_0(A_62))
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ v5_lattices(A_62)
      | ~ l2_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_227,plain,(
    ! [B_63,C_64] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_63,C_64),'#skF_7') = k1_lattices('#skF_4',B_63,k1_lattices('#skF_4',C_64,'#skF_7'))
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_4'))
      | ~ v5_lattices('#skF_4')
      | ~ l2_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_217])).

tff(c_239,plain,(
    ! [B_63,C_64] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_63,C_64),'#skF_7') = k1_lattices('#skF_4',B_63,k1_lattices('#skF_4',C_64,'#skF_7'))
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_227])).

tff(c_512,plain,(
    ! [B_76,C_77] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_76,C_77),'#skF_7') = k1_lattices('#skF_4',B_76,k1_lattices('#skF_4',C_77,'#skF_7'))
      | ~ m1_subset_1(C_77,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_239])).

tff(c_523,plain,(
    ! [B_76] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_76,'#skF_6'),'#skF_7') = k1_lattices('#skF_4',B_76,k1_lattices('#skF_4','#skF_6','#skF_7'))
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_24,c_512])).

tff(c_544,plain,(
    ! [B_78] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_78,'#skF_6'),'#skF_7') = k1_lattices('#skF_4',B_78,'#skF_7')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_523])).

tff(c_565,plain,(
    k1_lattices('#skF_4',k1_lattices('#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_lattices('#skF_4','#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_544])).

tff(c_582,plain,(
    k1_lattices('#skF_4','#skF_5','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_565])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  %$ r1_lattices > m1_subset_1 > v5_lattices > v2_struct_0 > l2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.35  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.65/1.35  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.65/1.35  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.65/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.65/1.35  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.35  
% 2.65/1.37  tff(f_81, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v5_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, D)) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_lattices)).
% 2.65/1.37  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 2.65/1.37  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v5_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k1_lattices(A, B, k1_lattices(A, C, D)) = k1_lattices(A, k1_lattices(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_lattices)).
% 2.65/1.37  tff(c_16, plain, (~r1_lattices('#skF_4', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_26, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_28, plain, (l2_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_22, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_57, plain, (![A_51, B_52, C_53]: (r1_lattices(A_51, B_52, C_53) | k1_lattices(A_51, B_52, C_53)!=C_53 | ~m1_subset_1(C_53, u1_struct_0(A_51)) | ~m1_subset_1(B_52, u1_struct_0(A_51)) | ~l2_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.65/1.37  tff(c_67, plain, (![B_52]: (r1_lattices('#skF_4', B_52, '#skF_7') | k1_lattices('#skF_4', B_52, '#skF_7')!='#skF_7' | ~m1_subset_1(B_52, u1_struct_0('#skF_4')) | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_57])).
% 2.65/1.37  tff(c_79, plain, (![B_52]: (r1_lattices('#skF_4', B_52, '#skF_7') | k1_lattices('#skF_4', B_52, '#skF_7')!='#skF_7' | ~m1_subset_1(B_52, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_67])).
% 2.65/1.37  tff(c_126, plain, (![B_55]: (r1_lattices('#skF_4', B_55, '#skF_7') | k1_lattices('#skF_4', B_55, '#skF_7')!='#skF_7' | ~m1_subset_1(B_55, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_32, c_79])).
% 2.65/1.37  tff(c_147, plain, (r1_lattices('#skF_4', '#skF_5', '#skF_7') | k1_lattices('#skF_4', '#skF_5', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_26, c_126])).
% 2.65/1.37  tff(c_166, plain, (k1_lattices('#skF_4', '#skF_5', '#skF_7')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_16, c_147])).
% 2.65/1.37  tff(c_24, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_18, plain, (r1_lattices('#skF_4', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_36, plain, (![A_48, B_49, C_50]: (k1_lattices(A_48, B_49, C_50)=C_50 | ~r1_lattices(A_48, B_49, C_50) | ~m1_subset_1(C_50, u1_struct_0(A_48)) | ~m1_subset_1(B_49, u1_struct_0(A_48)) | ~l2_lattices(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.65/1.37  tff(c_40, plain, (k1_lattices('#skF_4', '#skF_6', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_18, c_36])).
% 2.65/1.37  tff(c_47, plain, (k1_lattices('#skF_4', '#skF_6', '#skF_7')='#skF_7' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_22, c_40])).
% 2.65/1.37  tff(c_48, plain, (k1_lattices('#skF_4', '#skF_6', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_32, c_47])).
% 2.65/1.37  tff(c_20, plain, (r1_lattices('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_38, plain, (k1_lattices('#skF_4', '#skF_5', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_20, c_36])).
% 2.65/1.37  tff(c_43, plain, (k1_lattices('#skF_4', '#skF_5', '#skF_6')='#skF_6' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_38])).
% 2.65/1.37  tff(c_44, plain, (k1_lattices('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_32, c_43])).
% 2.65/1.37  tff(c_30, plain, (v5_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.37  tff(c_217, plain, (![A_62, B_63, C_64, D_65]: (k1_lattices(A_62, k1_lattices(A_62, B_63, C_64), D_65)=k1_lattices(A_62, B_63, k1_lattices(A_62, C_64, D_65)) | ~m1_subset_1(D_65, u1_struct_0(A_62)) | ~m1_subset_1(C_64, u1_struct_0(A_62)) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~v5_lattices(A_62) | ~l2_lattices(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.65/1.37  tff(c_227, plain, (![B_63, C_64]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_63, C_64), '#skF_7')=k1_lattices('#skF_4', B_63, k1_lattices('#skF_4', C_64, '#skF_7')) | ~m1_subset_1(C_64, u1_struct_0('#skF_4')) | ~m1_subset_1(B_63, u1_struct_0('#skF_4')) | ~v5_lattices('#skF_4') | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_217])).
% 2.65/1.37  tff(c_239, plain, (![B_63, C_64]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_63, C_64), '#skF_7')=k1_lattices('#skF_4', B_63, k1_lattices('#skF_4', C_64, '#skF_7')) | ~m1_subset_1(C_64, u1_struct_0('#skF_4')) | ~m1_subset_1(B_63, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_227])).
% 2.65/1.37  tff(c_512, plain, (![B_76, C_77]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_76, C_77), '#skF_7')=k1_lattices('#skF_4', B_76, k1_lattices('#skF_4', C_77, '#skF_7')) | ~m1_subset_1(C_77, u1_struct_0('#skF_4')) | ~m1_subset_1(B_76, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_32, c_239])).
% 2.65/1.37  tff(c_523, plain, (![B_76]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_76, '#skF_6'), '#skF_7')=k1_lattices('#skF_4', B_76, k1_lattices('#skF_4', '#skF_6', '#skF_7')) | ~m1_subset_1(B_76, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_24, c_512])).
% 2.65/1.37  tff(c_544, plain, (![B_78]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_78, '#skF_6'), '#skF_7')=k1_lattices('#skF_4', B_78, '#skF_7') | ~m1_subset_1(B_78, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_523])).
% 2.65/1.37  tff(c_565, plain, (k1_lattices('#skF_4', k1_lattices('#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_lattices('#skF_4', '#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_26, c_544])).
% 2.65/1.37  tff(c_582, plain, (k1_lattices('#skF_4', '#skF_5', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_565])).
% 2.65/1.37  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_582])).
% 2.65/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  Inference rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Ref     : 0
% 2.65/1.37  #Sup     : 111
% 2.65/1.37  #Fact    : 0
% 2.65/1.37  #Define  : 0
% 2.65/1.37  #Split   : 6
% 2.65/1.37  #Chain   : 0
% 2.65/1.37  #Close   : 0
% 2.65/1.37  
% 2.65/1.37  Ordering : KBO
% 2.65/1.37  
% 2.65/1.37  Simplification rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Subsume      : 0
% 2.65/1.37  #Demod        : 94
% 2.65/1.37  #Tautology    : 69
% 2.65/1.37  #SimpNegUnit  : 43
% 2.65/1.37  #BackRed      : 0
% 2.65/1.37  
% 2.65/1.37  #Partial instantiations: 0
% 2.65/1.37  #Strategies tried      : 1
% 2.65/1.37  
% 2.65/1.37  Timing (in seconds)
% 2.65/1.37  ----------------------
% 2.65/1.37  Preprocessing        : 0.29
% 2.65/1.37  Parsing              : 0.16
% 2.65/1.37  CNF conversion       : 0.03
% 2.65/1.37  Main loop            : 0.31
% 2.65/1.37  Inferencing          : 0.11
% 2.65/1.37  Reduction            : 0.10
% 2.65/1.37  Demodulation         : 0.07
% 2.65/1.37  BG Simplification    : 0.02
% 2.65/1.37  Subsumption          : 0.06
% 2.65/1.37  Abstraction          : 0.02
% 2.65/1.37  MUC search           : 0.00
% 2.65/1.37  Cooper               : 0.00
% 2.65/1.37  Total                : 0.63
% 2.65/1.37  Index Insertion      : 0.00
% 2.65/1.37  Index Deletion       : 0.00
% 2.65/1.37  Index Matching       : 0.00
% 2.65/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
